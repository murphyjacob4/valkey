# Adversarial and specification tests for Raft append-time validation and
# config-on-append.
#
# Step 1 tests reproduce bugs present in the config-on-apply / apply-time-
# validation base (must FAIL on base, PASS on the new design):
#   - DEL_VOTER apply reading node-local rs->leader (pure apply violation)
#   - DEL_VOTER apply divergence across 3 real nodes
#   - A2: pipelined voter changes committing with old quorum and losing a
#     committed entry
#   - Single-node fast-commit and quorum growth respecting projected voters
#   - Racing proposals turning into committed no-ops at apply
#
# Step 2 tests verify the new design's invariants:
#   - Truncation of an uncommitted voter change rolls back effective voters
#   - Restart rebuilds the projected voter set from the persisted log tail
#   - At most one uncommitted voter change in the log
#   - New leader cannot propose a voter change before committing its own-term entry
#   - NODE_JOIN ... voter rejected except empty-log bootstrap self-join
#   - NODE_FORGET of a voter rejected

source tests/support/cluster_raft.tcl

# --------------------------------------------------------------------------
# Wire-protocol helpers (self-contained to avoid conflicts with other suites)
# --------------------------------------------------------------------------

proc rca_msg {payload} {
    set len [expr {8 + [string length $payload]}]
    set hdr "RAFT"
    append hdr [binary format I $len]
    append hdr $payload
    return $hdr
}

proc rca_connect {host port} {
    set fd [socket $host $port]
    fconfigure $fd -translation binary -buffering full
    return $fd
}

proc rca_send {fd payload} {
    puts -nonewline $fd [rca_msg $payload]
    flush $fd
}

proc rca_recv {fd {timeout 5000}} {
    fconfigure $fd -blocking 0
    set deadline [expr {[clock milliseconds] + $timeout}]
    set hdr ""
    while {[string length $hdr] < 8} {
        append hdr [read $fd [expr {8 - [string length $hdr]}]]
        if {[string length $hdr] < 8} {
            if {[clock milliseconds] > $deadline} {
                error "timeout reading raft header"
            }
            after 10
        }
    }
    if {[string range $hdr 0 3] ne "RAFT"} {
        error "bad raft header: [string range $hdr 0 3]"
    }
    binary scan [string range $hdr 4 7] I totlen
    set paylen [expr {$totlen - 8}]
    set payload ""
    while {[string length $payload] < $paylen} {
        append payload [read $fd [expr {$paylen - [string length $payload]}]]
        if {[string length $payload] < $paylen} {
            if {[clock milliseconds] > $deadline} {
                error "timeout reading raft payload (got [string length $payload]/$paylen)"
            }
            after 10
        }
    }
    return $payload
}

proc rca_recv_until {fd pattern {timeout 5000}} {
    set deadline [expr {[clock milliseconds] + $timeout}]
    while {1} {
        set rem [expr {$deadline - [clock milliseconds]}]
        if {$rem <= 0} {
            error "timeout waiting for message matching '$pattern'"
        }
        set msg [rca_recv $fd $rem]
        if {[string match $pattern $msg]} {return $msg}
    }
}

proc rca_try_recv_matching {fd pattern {timeout 1000}} {
    set deadline [expr {[clock milliseconds] + $timeout}]
    while {1} {
        set rem [expr {$deadline - [clock milliseconds]}]
        if {$rem <= 0} {return ""}
        if {[catch {set msg [rca_recv $fd $rem]}]} {return ""}
        if {[string match $pattern $msg]} {return $msg}
    }
}

proc rca_listen {port_var} {
    upvar $port_var listen_port
    set key [incr ::_rca_listen_seq]
    set ::_rca_accepted($key) ""
    set listen_fd [socket -server [list _rca_on_accept $key] -myaddr 127.0.0.1 0]
    set ::_rca_listen_key($listen_fd) $key
    set listen_port [lindex [fconfigure $listen_fd -sockname] 2]
    return $listen_fd
}

proc _rca_on_accept {key fd addr port} {
    fconfigure $fd -translation binary -buffering full
    set ::_rca_accepted($key) $fd
}

proc rca_accept {listen_fd {timeout 5000}} {
    set key $::_rca_listen_key($listen_fd)
    if {$::_rca_accepted($key) eq ""} {
        set accept_after [after $timeout [list set ::_rca_accepted($key) timeout]]
        vwait ::_rca_accepted($key)
        after cancel $accept_after
    }
    close $listen_fd
    set fd $::_rca_accepted($key)
    unset ::_rca_accepted($key) ::_rca_listen_key($listen_fd)
    if {$fd eq "timeout"} {
        error "timeout waiting for connection"
    }
    return $fd
}

proc rca_listen_and_accept {port_var {timeout 5000} {before_accept {}}} {
    upvar $port_var listen_port
    set listen_fd [rca_listen listen_port]
    if {$before_accept ne {}} {
        uplevel 1 $before_accept
    }
    return [rca_accept $listen_fd $timeout]
}

proc rca_connect_fake_node {host cport fake_id fake_addr} {
    set fd [rca_connect $host $cport]
    rca_send $fd "HELLO $fake_id $fake_addr"
    set reply [rca_recv $fd]
    assert_match "HI *" $reply
    return $fd
}

proc rca_ae_header {msg} {
    return [split [lindex [split $msg "\n"] 0] " "]
}

proc rca_reply_ae_ack {fd ae_msg {repl_offset 0}} {
    set fields [rca_ae_header $ae_msg]
    set term [lindex $fields 2]
    set prev_idx [lindex $fields 3]
    set count [lindex $fields 6]
    set last_index [expr {$prev_idx + $count}]
    rca_send $fd "AE_ACK $term 1 $last_index $repl_offset"
    return $last_index
}

# Drain any buffered messages on fd without blocking, optionally acking AEs.
proc rca_drain_and_ack {fd {ack 1}} {
    fconfigure $fd -blocking 0
    set last_idx 0
    while {1} {
        if {[catch {set msg [rca_recv $fd 20]}]} break
        if {$ack && [string match "AE *" $msg]} {
            set idx [rca_reply_ae_ack $fd $msg 0]
            if {$idx > $last_idx} {set last_idx $idx}
        }
    }
    return $last_idx
}

# Wait until fd receives an AE whose prev+count >= target_idx and ack it.
# Returns the highest index acked.
proc rca_ack_up_to {fd target_idx {timeout 5000}} {
    set deadline [expr {[clock milliseconds] + $timeout}]
    set max_idx 0
    while {$max_idx < $target_idx} {
        set rem [expr {$deadline - [clock milliseconds]}]
        if {$rem <= 0} {
            error "timeout waiting to ack up to index $target_idx (got $max_idx)"
        }
        set msg [rca_recv $fd $rem]
        if {[string match "AE *" $msg]} {
            set idx [rca_reply_ae_ack $fd $msg 0]
            if {$idx > $max_idx} {set max_idx $idx}
        }
    }
    return $max_idx
}

# Wait until every fd in fds has received and acked up to target_idx.
proc rca_ack_all_up_to {fds target_idx {timeout 5000}} {
    set deadline [expr {[clock milliseconds] + $timeout}]
    array set acked {}
    foreach fd $fds {set acked($fd) 0}
    while {1} {
        set all_done 1
        foreach fd $fds {
            if {$acked($fd) < $target_idx} {
                set all_done 0
                if {![catch {set msg [rca_recv $fd 30]}]} {
                    if {[string match "AE *" $msg]} {
                        set idx [rca_reply_ae_ack $fd $msg 0]
                        if {$idx > $acked($fd)} {set acked($fd) $idx}
                    }
                }
            }
        }
        if {$all_done} return
        if {[clock milliseconds] > $deadline} {
            set diag {}
            foreach fd $fds {lappend diag "$fd=$acked($fd)"}
            error "timeout waiting for all fake nodes to ack index $target_idx (got: $diag, last_applied=[CI 0 cluster_raft_last_applied], commit=[CI 0 cluster_raft_commit_index])"
        }
    }
}

# Wait until the real server's commit_index reaches target_idx while all fds in
# active_fds ack AEs.
proc rca_drive_commit {active_fds target_idx {srv_idx 0} {timeout 5000}} {
    set deadline [expr {[clock milliseconds] + $timeout}]
    while {[CI $srv_idx cluster_raft_commit_index] < $target_idx} {
        foreach fd $active_fds {
            rca_drain_and_ack $fd 1
        }
        if {[clock milliseconds] > $deadline} {
            error "timeout waiting for commit_index >= $target_idx (current=[CI $srv_idx cluster_raft_commit_index])"
        }
        after 20
    }
    # Drain one more round so active_fds have also acked up to target_idx.
    foreach fd $active_fds {
        rca_drain_and_ack $fd 1
    }
}

# Have real server 0 (leader) MEET a fake node, which joins as a learner.
# active_fds are existing fake peers that may need to ack so NODE_JOIN commits.
# Returns {fd fake_addr}.
proc rca_join_fake_learner {fake_id fake_shard {active_fds {}}} {
    set cport 0
    set fd [rca_listen_and_accept cport 5000 {
        set fake_port [expr {$cport - 10000}]
        set fake_addr "127.0.0.1:${fake_port}@${cport},,tls-port=0,shard-id=$fake_shard"
        set meet_client [valkey_deferring_client]
        $meet_client CLUSTER MEET 127.0.0.1 $fake_port
    }]

    assert_match "HELLO *" [rca_recv $fd 5000]
    assert_match "MEET *" [rca_recv $fd 5000]
    rca_send $fd "HI $fake_id $fake_addr"
    rca_send $fd "ADD_ME"

    # Drive AE_ACKs on existing voters + the new learner until MEET completes
    # and the new learner's NODE_JOIN is committed (learner flag applied).
    set all_fds [concat $active_fds [list $fd]]
    set deadline [expr {[clock milliseconds] + 5000}]
    while {![raft_node_has_flag [srv 0 client] $fake_id learner]} {
        foreach afd $all_fds {rca_drain_and_ack $afd 1}
        if {[clock milliseconds] > $deadline} {
            error "timeout waiting for fake learner $fake_id to join (nodes=[R 0 CLUSTER NODES])"
        }
        after 20
    }
    assert_equal "OK" [$meet_client read]
    $meet_client close

    # Make sure all_fds are caught up to the committed NODE_JOIN index.
    set last [CI 0 cluster_raft_last_applied]
    rca_ack_all_up_to $all_fds $last 5000
    return [list $fd $fake_addr]
}

# Promote a fake learner to voter on real server 0 while active_fds ack AEs.
proc rca_promote_fake_voter {fake_id active_fds} {
    set target_idx [expr {[CI 0 cluster_raft_commit_index] + 1}]
    set rd [valkey_deferring_client]
    $rd CLUSTER ADDVOTER $fake_id
    rca_drive_commit $active_fds $target_idx 0 5000
    assert_equal "OK" [$rd read]
    $rd close
    rca_ack_all_up_to $active_fds [CI 0 cluster_raft_last_applied] 5000
}

# Seed a real server (via fake leader fd) using contract-compliant entries:
#   index 1: NODE_JOIN <leader_id> <leader_addr> voter (bootstrap self-join)
#   then for each {id addr is_voter} in peers:
#     NODE_JOIN <id> <addr> learner (committed)
#     if is_voter: ADD_VOTER <id> (committed)
# Returns the final committed log index.
proc rca_seed_cluster {fd leader_id leader_addr peers {term 1}} {
    set idx 1
    rca_send $fd "AE $leader_id $term 0 0 $idx 1\n$term NODE_JOIN $leader_id $leader_addr voter"
    assert_match "AE_ACK $term 1 $idx *" [rca_recv_until $fd "AE_ACK *"]

    foreach spec $peers {
        lassign $spec id addr is_voter
        set prev $idx
        incr idx
        rca_send $fd "AE $leader_id $term $prev $term $idx 1\n$term NODE_JOIN $id $addr learner"
        assert_match "AE_ACK $term 1 $idx *" [rca_recv_until $fd "AE_ACK *"]
        if {$is_voter} {
            set prev $idx
            incr idx
            rca_send $fd "AE $leader_id $term $prev $term $idx 1\n$term ADD_VOTER $id"
            assert_match "AE_ACK $term 1 $idx *" [rca_recv_until $fd "AE_ACK *"]
        }
    }
    return $idx
}

# Event-loop-friendly sleep/wait for tests that run a Tcl fileevent proxy.
proc rca_sleep_ev {ms} {
    set key [incr ::_rca_ev_seq]
    after $ms [list set ::_rca_ev($key) 1]
    vwait ::_rca_ev($key)
    unset ::_rca_ev($key)
}

proc rca_wait_ev {maxtries delay expr_body} {
    for {set i 0} {$i < $maxtries} {incr i} {
        if {[uplevel 1 [list expr $expr_body]]} {return 1}
        rca_sleep_ev $delay
    }
    return 0
}

# Transparent RAFT-framed TCP proxy for intercepting/dropping specific frames
# between real valkey-server instances.
proc rca_proxy_start {upstream_port filter_proc} {
    set id [incr ::_rca_proxy_seq]
    set ::_rca_proxy($id,upstream_port) $upstream_port
    set ::_rca_proxy($id,filter) $filter_proc
    set ::_rca_proxy($id,conns) {}
    set listen_fd [socket -server [list _rca_proxy_accept $id] -myaddr 127.0.0.1 0]
    set ::_rca_proxy($id,listen_fd) $listen_fd
    set port [lindex [fconfigure $listen_fd -sockname] 2]
    return [list $id $port]
}

proc _rca_proxy_accept {id client_fd addr port} {
    fconfigure $client_fd -translation binary -buffering none -blocking 0
    if {[catch {set up_fd [socket 127.0.0.1 $::_rca_proxy($id,upstream_port)]}]} {
        catch {close $client_fd}
        return
    }
    fconfigure $up_fd -translation binary -buffering none -blocking 0
    lappend ::_rca_proxy($id,conns) $client_fd $up_fd
    set ::_rca_pbuf($client_fd) ""
    set ::_rca_pbuf($up_fd) ""
    fileevent $client_fd readable [list _rca_proxy_read $id $client_fd $up_fd c2s]
    fileevent $up_fd readable [list _rca_proxy_read $id $up_fd $client_fd s2c]
}

proc _rca_proxy_close_pair {fd1 fd2} {
    foreach fd [list $fd1 $fd2] {
        catch {fileevent $fd readable {}}
        catch {close $fd}
        unset -nocomplain ::_rca_pbuf($fd)
    }
}

proc _rca_proxy_read {id src dst dir} {
    if {[catch {set data [read $src]}] || ([string length $data] == 0 && [eof $src])} {
        _rca_proxy_close_pair $src $dst
        return
    }
    append ::_rca_pbuf($src) $data
    while {[string length $::_rca_pbuf($src)] >= 8} {
        set hdr [string range $::_rca_pbuf($src) 0 7]
        if {[string range $hdr 0 3] ne "RAFT"} {
            # Non-RAFT bytes (should not happen); forward raw.
            set raw $::_rca_pbuf($src)
            set ::_rca_pbuf($src) ""
            if {[catch {puts -nonewline $dst $raw}]} {
                _rca_proxy_close_pair $src $dst
            }
            return
        }
        binary scan [string range $hdr 4 7] I totlen
        if {[string length $::_rca_pbuf($src)] < $totlen} break
        set frame [string range $::_rca_pbuf($src) 0 [expr {$totlen - 1}]]
        set payload [string range $frame 8 end]
        set ::_rca_pbuf($src) [string range $::_rca_pbuf($src) $totlen end]

        set filter $::_rca_proxy($id,filter)
        set action "forward"
        if {$filter ne ""} {
            set action [{*}$filter $dir $payload]
        }
        if {$action eq "forward"} {
            if {[catch {puts -nonewline $dst $frame}]} {
                _rca_proxy_close_pair $src $dst
                return
            }
        }
    }
}

proc rca_proxy_stop {id} {
    catch {close $::_rca_proxy($id,listen_fd)}
    if {[info exists ::_rca_proxy($id,conns)]} {
        foreach fd $::_rca_proxy($id,conns) {
            catch {fileevent $fd readable {}}
            catch {close $fd}
            unset -nocomplain ::_rca_pbuf($fd)
        }
    }
    array unset ::_rca_proxy "$id,*"
}

tags {tls:skip external:skip cluster singledb} {

# ==========================================================================
# Step 1(a-1): Pure apply of DEL_VOTER must not depend on rs->leader
# ==========================================================================
test "Raft config-append: DEL_VOTER apply must not depend on rs->leader" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 1000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set c_id [R 0 CLUSTER MYID]
        set c_addr "127.0.0.1:[srv 0 port]@$cport,,tls-port=0,shard-id=[string repeat 1 40]"
        set a_id [string repeat "a" 40]
        set a_addr "127.0.0.1:9901@19901,,tls-port=0,shard-id=[string repeat 2 40]"
        set b_id [string repeat "b" 40]
        set b_addr "127.0.0.1:9902@19902,,tls-port=0,shard-id=[string repeat 3 40]"

        set fd_a [rca_connect_fake_node 127.0.0.1 $cport $a_id $a_addr]
        rca_send $fd_a "MEET cluster"
        assert_match "ADD_ME*" [rca_recv $fd_a]

        set idx [rca_seed_cluster $fd_a $a_id $a_addr [list \
            [list $c_id $c_addr 1] \
            [list $b_id $b_addr 1]]]
        assert_equal 3 [CI 0 cluster_size]
        assert_equal $idx [CI 0 cluster_raft_last_applied]

        # Leader A replicates uncommitted DEL_VOTER B at idx+1.
        set del_idx [expr {$idx + 1}]
        rca_send $fd_a "AE $a_id 1 $idx 1 $idx 1\n1 DEL_VOTER $b_id"
        assert_match "AE_ACK 1 1 $del_idx *" [rca_recv_until $fd_a "AE_ACK *"]
        assert_equal $idx [CI 0 cluster_raft_last_applied]

        # Now B appears as leader in term 2 and commits del_idx + NOOP.
        # C's rs->leader becomes B before raftApplyCommitted() runs.
        # Under pure apply, DEL_VOTER B MUST still apply regardless of rs->leader.
        set fd_b [rca_connect_fake_node 127.0.0.1 $cport $b_id $b_addr]
        set noop_idx [expr {$del_idx + 1}]
        rca_send $fd_b "AE $b_id 2 $del_idx 1 $noop_idx 1\n2 NOOP "
        assert_match "AE_ACK 2 1 $noop_idx *" [rca_recv_until $fd_b "AE_ACK *"]

        assert_equal $noop_idx [CI 0 cluster_raft_last_applied]
        assert_equal 2 [CI 0 cluster_size]
        assert_equal 1 [raft_node_has_flag [srv 0 client] $b_id learner]

        close $fd_b
        close $fd_a
    }
}

# ==========================================================================
# Step 1(a-2): DEL_VOTER apply divergence across 3 real nodes
# ==========================================================================
test "Raft config-append: DEL_VOTER apply does not diverge across 3 real nodes" {
    start_multiple_servers 3 {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 1000}} {
        set a_id [R 0 CLUSTER MYID]
        set b_id [R 1 CLUSTER MYID]
        set c_id [R 2 CLUSTER MYID]

        set b_real_cport [expr {[srv -1 port] + 10000}]
        set c_real_cport [expr {[srv -2 port] + 10000}]

        # Configure proxy filter state (initially pass-through).
        set ::_rca_div_block_commit 0
        set ::_rca_div_drop_c_votes 0
        set ::_rca_div_a_id $a_id
        set ::_rca_div_c_id $c_id
        set ::_rca_div_del_idx 0

        proc _rca_div_filter {dir payload} {
            if {$::_rca_div_block_commit && [string match "AE $::_rca_div_a_id *" $payload]} {
                set fields [split [lindex [split $payload "\n"] 0] " "]
                set commit [lindex $fields 5]
                if {[string is integer -strict $commit] && $commit >= $::_rca_div_del_idx} {
                    return "drop"
                }
            }
            if {$::_rca_div_drop_c_votes} {
                if {[string match "PRE_VOTE_REQ $::_rca_div_c_id *" $payload] ||
                    [string match "VOTE_REQ $::_rca_div_c_id *" $payload]} {
                    return "drop"
                }
            }
            return "forward"
        }

        lassign [rca_proxy_start $b_real_cport _rca_div_filter] pb_id pb_port
        lassign [rca_proxy_start $c_real_cport _rca_div_filter] pc_id pc_port

        set cleanup_err ""
        if {[catch {
            # Point B and C's announced bus ports at the proxies before MEET.
            R 1 CONFIG SET cluster-announce-bus-port $pb_port
            R 2 CONFIG SET cluster-announce-bus-port $pc_port

            set rd1 [valkey_deferring_client 0]
            $rd1 CLUSTER MEET 127.0.0.1 [srv -1 port] $pb_port
            assert [rca_wait_ev 100 50 {[raft_node_visible [srv 0 client] $b_id] && ![raft_node_has_flag [srv 0 client] $b_id handshake]}]
            assert_equal "OK" [$rd1 read]
            $rd1 close

            set rd2 [valkey_deferring_client 0]
            $rd2 CLUSTER MEET 127.0.0.1 [srv -2 port] $pc_port
            assert [rca_wait_ev 100 50 {[raft_node_visible [srv 0 client] $c_id] && ![raft_node_has_flag [srv 0 client] $c_id handshake]}]
            assert_equal "OK" [$rd2 read]
            $rd2 close

            # Promote B and C to voters while pumping proxy events (retry until caught up).
            foreach vid [list $b_id $c_id] {
                assert [rca_wait_ev 100 50 {[raft_node_has_flag [srv 0 client] $vid learner]}]
                set promoted 0
                for {set attempt 0} {$attempt < 40 && !$promoted} {incr attempt} {
                    set rd [valkey_deferring_client 0]
                    $rd CLUSTER ADDVOTER $vid
                    set got_res [rca_wait_ev 40 50 {![raft_node_has_flag [srv 0 client] $vid learner]}]
                    set reply_err ""
                    if {[catch {set r [$rd read]} reply_err]} {
                        $rd close
                        rca_sleep_ev 50
                        continue
                    }
                    $rd close
                    if {$r eq "OK"} {set promoted 1}
                }
                assert_equal 1 $promoted
            }
            assert [rca_wait_ev 100 50 {
                [CI 0 cluster_size] == 3 &&
                [CI 1 cluster_size] == 3 &&
                [CI 2 cluster_size] == 3
            }]

            # Wait until all 3 nodes are at the same last_applied.
            assert [rca_wait_ev 100 50 {
                [CI 0 cluster_raft_last_applied] == [CI 1 cluster_raft_last_applied] &&
                [CI 0 cluster_raft_last_applied] == [CI 2 cluster_raft_last_applied]
            }]

            # Arm proxy: let DEL_VOTER B AE (with old commit) and its AE_ACKs
            # through, but drop A's subsequent commit AE (commit >= del_idx).
            set del_idx [expr {[CI 0 cluster_raft_commit_index] + 1}]
            set ::_rca_div_del_idx $del_idx
            set ::_rca_div_block_commit 1
            set ::_rca_div_drop_c_votes 1

            # Demote B on leader A.
            set rd_del [valkey_deferring_client 0]
            $rd_del CLUSTER DELVOTER $b_id

            # Wait for A to commit and apply DEL_VOTER B locally.
            assert [rca_wait_ev 100 50 {[CI 0 cluster_size] == 2 && [CI 0 cluster_raft_last_applied] >= $del_idx}]
            assert_equal "OK" [$rd_del read]
            $rd_del close

            # Pause A before B or C receives commit >= del_idx.
            pause_process [srv 0 pid]

            # Give B time to try winning an election against C (on base, B wins
            # because DEL_VOTER B is uncommitted; on config-on-append, B cannot
            # win because DEL_VOTER B already removed B from projected voters).
            set b_won [rca_wait_ev 70 50 {[CI 1 cluster_raft_role] eq "leader"}]
            if {$b_won} {
                # Wait for B to commit its new-term entry (and skip DEL_VOTER B on base).
                rca_wait_ev 60 50 {[CI 1 cluster_raft_last_applied] > $del_idx && [CI 2 cluster_raft_last_applied] > $del_idx}
            }

            # Disarm proxy filters and resume A so all 3 nodes converge.
            set ::_rca_div_block_commit 0
            set ::_rca_div_drop_c_votes 0
            resume_process [srv 0 pid]

            # Wait for all 3 nodes to reach the same last_applied >= del_idx.
            assert [rca_wait_ev 120 100 {
                [CI 0 cluster_raft_last_applied] >= $del_idx &&
                [CI 0 cluster_raft_last_applied] == [CI 1 cluster_raft_last_applied] &&
                [CI 0 cluster_raft_last_applied] == [CI 2 cluster_raft_last_applied]
            }]

            # All 3 nodes MUST agree on cluster_size == 2 and B being a learner.
            set s0 [CI 0 cluster_size]
            set s1 [CI 1 cluster_size]
            set s2 [CI 2 cluster_size]
            set l0 [raft_node_has_flag [srv 0 client] $b_id learner]
            set l1 [raft_node_has_flag [srv -1 client] $b_id learner]
            set l2 [raft_node_has_flag [srv -2 client] $b_id learner]
            assert_equal [list 2 2 2 1 1 1] [list $s0 $s1 $s2 $l0 $l1 $l2] \
                "DEL_VOTER apply diverged across nodes (sizes=$s0,$s1,$s2 b_learner=$l0,$l1,$l2 b_won=$b_won)"
        } cleanup_err]} {
            catch {resume_process [srv 0 pid]}
            rca_proxy_stop $pb_id
            rca_proxy_stop $pc_id
            error $cleanup_err
        }
        rca_proxy_stop $pb_id
        rca_proxy_stop $pc_id
    }
}

# ==========================================================================
# Step 1(b-1): A2 — pipelined voter changes + old-quorum commit loses entry
# ==========================================================================
test "Raft config-append: A2 pipelined voter changes cannot commit entry with old quorum" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000}} {
        set a_id [R 0 CLUSTER MYID]
        set b_id [string repeat "b" 40]
        set c_id [string repeat "c" 40]
        set d_id [string repeat "d" 40]
        set e_id [string repeat "e" 40]

        lassign [rca_join_fake_learner $b_id [string repeat "2" 40]] fd_b b_addr
        rca_promote_fake_voter $b_id [list $fd_b]
        assert_equal 2 [CI 0 cluster_size]

        lassign [rca_join_fake_learner $c_id [string repeat "3" 40] [list $fd_b]] fd_c c_addr
        lassign [rca_join_fake_learner $d_id [string repeat "4" 40] [list $fd_b $fd_c]] fd_d d_addr
        lassign [rca_join_fake_learner $e_id [string repeat "5" 40] [list $fd_b $fd_c $fd_d]] fd_e e_addr
        assert_equal 2 [CI 0 cluster_size]

        set base_commit [CI 0 cluster_raft_commit_index]
        set term [CI 0 cluster_raft_current_term]

        # B stops acking so ADD_VOTER C stays uncommitted.
        set rd_c [valkey_deferring_client]
        $rd_c CLUSTER ADDVOTER $c_id
        set idx_c [expr {$base_commit + 1}]
        rca_ack_all_up_to [list $fd_c $fd_d $fd_e] $idx_c 5000
        assert_equal $base_commit [CI 0 cluster_raft_commit_index]

        # Attempt to pipeline a second uncommitted voter change (ADD_VOTER D).
        set err ""
        set d_rejected 0
        set rd_d [valkey_deferring_client]
        $rd_d CLUSTER ADDVOTER $d_id

        # Check whether the leader immediately rejected ADD_VOTER D (new design)
        # or appended it (base).
        set got_d_on_c [rca_try_recv_matching $fd_c "AE *ADD_VOTER $d_id*" 500]
        if {$got_d_on_c eq ""} {
            # New design rejected pipelined ADD_VOTER D before append!
            set d_rejected 1
            assert_error "*" {$rd_d read}
            $rd_d close
            # Now let B ack idx_c; ADD_VOTER C should commit cleanly.
            rca_drive_commit [list $fd_b $fd_c $fd_d $fd_e] $idx_c 0 5000
            assert_equal "OK" [$rd_c read]
            $rd_c close
            assert_equal 3 [CI 0 cluster_size]
        } else {
            # Base allowed pipelining ADD_VOTER D! Execute the full A2 attack
            # to confirm it commits a SLOT_CHANGE using only old quorum {A, B}
            # while {C, D, E} (a 3/5 majority of the new voters) never got it.
            set idx_d [expr {$idx_c + 1}]
            rca_reply_ae_ack $fd_c $got_d_on_c 0
            rca_ack_all_up_to [list $fd_d $fd_e] $idx_d 5000

            set rd_e [valkey_deferring_client]
            $rd_e CLUSTER ADDVOTER $e_id
            set idx_e [expr {$idx_d + 1}]
            rca_ack_all_up_to [list $fd_c $fd_d $fd_e] $idx_e 5000

            # Append a data-plane entry (SLOT_CHANGE) at idx_slot.
            # C, D, E do NOT receive or ack idx_slot!
            set rd_slot [valkey_deferring_client]
            $rd_slot CLUSTER ADDSLOTS 0
            set idx_slot [expr {$idx_e + 1}]

            # Drain B's inbound AEs without acking individually, then send a
            # single AE_ACK for idx_slot (as if B received 7..idx_slot in one
            # batch). Only {A, B} (old quorum = 2/2) have idx_slot!
            set deadline [expr {[clock milliseconds] + 5000}]
            set b_got 0
            while {$b_got < $idx_slot} {
                set msg [rca_recv $fd_b [expr {max(1, $deadline - [clock milliseconds])}]]
                if {[string match "AE *" $msg]} {
                    set fields [rca_ae_header $msg]
                    set last [expr {[lindex $fields 3] + [lindex $fields 6]}]
                    if {$last > $b_got} {set b_got $last}
                }
            }
            rca_send $fd_b "AE_ACK $term 1 $idx_slot 0"
            wait_for_condition 50 50 {[CI 0 cluster_raft_commit_index] >= $idx_slot} else {
                fail "expected base to commit idx_slot=$idx_slot with old quorum"
            }
            assert_equal "OK" [$rd_c read]
            assert_equal "OK" [$rd_d read]
            assert_equal "OK" [$rd_e read]
            assert_equal "OK" [$rd_slot read]
            $rd_c close; $rd_d close; $rd_e close; $rd_slot close

            # A committed SLOT_CHANGE at idx_slot and now has size=5,
            # while {C, D, E} (3/5 majority) only have logs up to idx_e!
            assert_equal 5 [CI 0 cluster_size]
            assert_equal 1 [CI 0 cluster_slots_assigned]
            fail "A2 bug reproduced: leader committed SLOT_CHANGE at index $idx_slot with only old quorum {A,B} (2 of 5 voters) while majority {C,D,E} only have up to index $idx_e"
        }
        assert_equal 1 $d_rejected

        foreach fd [list $fd_b $fd_c $fd_d $fd_e] {close $fd}
    }
}

# ==========================================================================
# Step 1(b-2): Single-node fast-commit and quorum growth use projected voters
# ==========================================================================
test "Raft config-append: single-node fast-commit and quorum growth use projected voters" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000}} {
        set b_id [string repeat "b" 40]
        set c_id [string repeat "c" 40]
        set d_id [string repeat "d" 40]

        # Part 1: 1 voter {A} + 1 learner {B}.
        # Appending ADD_VOTER B changes effective voters to {A, B} (quorum=2).
        # A must NOT fast-commit ADD_VOTER B without B's AE_ACK.
        lassign [rca_join_fake_learner $b_id [string repeat "2" 40]] fd_b b_addr
        assert_equal 1 [CI 0 cluster_size]
        set commit_before [CI 0 cluster_raft_commit_index]
        set add_b_idx [expr {$commit_before + 1}]

        set rd [valkey_deferring_client]
        $rd CLUSTER ADDVOTER $b_id

        # Wait for A to send AE with ADD_VOTER B, but do NOT ack it yet.
        set ae_b [rca_recv_until $fd_b "AE *ADD_VOTER $b_id*" 5000]
        after 300
        assert_equal $commit_before [CI 0 cluster_raft_commit_index] \
            "single-node fast-commit committed ADD_VOTER B without B's ACK"
        assert_equal 1 [CI 0 cluster_size]

        # Now B acks ADD_VOTER B -> quorum {A, B} reached -> commits.
        rca_reply_ae_ack $fd_b $ae_b 0
        rca_drive_commit [list $fd_b] $add_b_idx 0 5000
        assert_equal "OK" [$rd read]
        $rd close
        assert_equal 2 [CI 0 cluster_size]

        # Part 2: Grow to 3 voters {A, B, C} + learner D.
        # Adding D grows effective voters to 4 (quorum=3).
        # Only B acking (A + B = 2 = old quorum of 3) must NOT commit ADD_VOTER D.
        lassign [rca_join_fake_learner $c_id [string repeat "3" 40] [list $fd_b]] fd_c c_addr
        rca_promote_fake_voter $c_id [list $fd_b $fd_c]
        lassign [rca_join_fake_learner $d_id [string repeat "4" 40] [list $fd_b $fd_c]] fd_d d_addr
        assert_equal 3 [CI 0 cluster_size]

        set commit_before [CI 0 cluster_raft_commit_index]
        set add_d_idx [expr {$commit_before + 1}]

        set rd [valkey_deferring_client]
        $rd CLUSTER ADDVOTER $d_id

        # Only B acks ADD_VOTER D (2 of 4 voters: old quorum, not new quorum).
        rca_ack_up_to $fd_b $add_d_idx 5000
        after 300
        assert_equal $commit_before [CI 0 cluster_raft_commit_index] \
            "leader committed ADD_VOTER D with only 2/4 acks (old quorum)"
        assert_equal 3 [CI 0 cluster_size]

        # Once C also acks (3 of 4 voters), ADD_VOTER D commits.
        rca_drive_commit [list $fd_b $fd_c $fd_d] $add_d_idx 0 5000
        assert_equal "OK" [$rd read]
        $rd close
        assert_equal 4 [CI 0 cluster_size]

        foreach fd [list $fd_b $fd_c $fd_d] {close $fd}
    }
}

# ==========================================================================
# Step 1(c): Committed entries must not become no-ops at apply
# ==========================================================================
test "Raft config-append: racing proposals rejected before append (no committed no-ops)" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000 loglevel debug}} {
        set a_id [R 0 CLUSTER MYID]
        set cport [expr {[srv 0 port] + 10000}]
        set b_id [string repeat "b" 40]
        set r1_id [string repeat "1" 40]
        set r2_id [string repeat "2" 40]
        set l_id [string repeat "3" 40]

        # Extract A's shard id.
        set a_shard ""
        foreach shard [R 0 CLUSTER SHARDS] {
            foreach node [dict get $shard nodes] {
                if {[dict get $node id] eq $a_id} {
                    set a_shard [dict get $shard id]
                }
            }
        }
        assert {$a_shard ne ""}

        # Form 2-voter cluster {A, B} + learners R1, R2, L.
        lassign [rca_join_fake_learner $b_id [string repeat "9" 40]] fd_b b_addr
        rca_promote_fake_voter $b_id [list $fd_b]
        set r1_shard [string repeat "4" 40]
        set r2_shard [string repeat "5" 40]
        set l_shard [string repeat "6" 40]
        lassign [rca_join_fake_learner $r1_id $r1_shard [list $fd_b]] fd_r1 r1_addr
        lassign [rca_join_fake_learner $r2_id $r2_shard [list $fd_b $fd_r1]] fd_r2 r2_addr
        lassign [rca_join_fake_learner $l_id $l_shard [list $fd_b $fd_r1 $fd_r2]] fd_l l_addr

        # Make R1 and R2 replicas of A in shard a_shard via PROPOSE.
        set in_r1 [rca_connect_fake_node 127.0.0.1 $cport $r1_id $r1_addr]
        set in_r2 [rca_connect_fake_node 127.0.0.1 $cport $r2_id $r2_addr]
        set in_l [rca_connect_fake_node 127.0.0.1 $cport $l_id $l_addr]

        set target [expr {[CI 0 cluster_raft_commit_index] + 1}]
        rca_send $in_r1 "PROPOSE SET_REPLICA_OF $r1_id $r1_shard 0 $a_id $a_shard 0"
        rca_drive_commit [list $fd_b $fd_r1 $fd_r2 $fd_l] $target 0 5000

        # A's shard epoch is now 1. Make R2 also a replica of A.
        set target [expr {[CI 0 cluster_raft_commit_index] + 1}]
        rca_send $in_r2 "PROPOSE SET_REPLICA_OF $r2_id $r2_shard 0 $a_id $a_shard 1"
        rca_drive_commit [list $fd_b $fd_r1 $fd_r2 $fd_l] $target 0 5000
        # A's shard epoch is now 2.

        # --- Sub-case 1: two racing FAILOVERs for the same shard while uncommitted ---
        set skipped_before [count_log_message 0 "Proposal rejected at apply"]
        set commit_before [CI 0 cluster_raft_commit_index]

        # B does not ack yet. R1 proposes FAILOVER at epoch 2.
        rca_send $in_r1 "PROPOSE FAILOVER $r1_id $a_id $a_shard 2"
        # Wait until leader appends R1's FAILOVER (visible via AE to fd_r1).
        set idx_f1 [expr {$commit_before + 1}]
        rca_ack_up_to $fd_r1 $idx_f1 5000
        assert_equal $commit_before [CI 0 cluster_raft_commit_index]

        # Now R2 races with FAILOVER at the SAME epoch 2 while R1's FAILOVER is uncommitted.
        # Validating against S_p must reject R2 BEFORE append (sending REJECT).
        rca_send $in_r2 "PROPOSE FAILOVER $r2_id $a_id $a_shard 2"
        set rej [rca_try_recv_matching $in_r2 "REJECT *" 1000]
        assert_match "REJECT *" $rej

        # Commit and verify ONLY idx_f1 was appended and ZERO entries were skipped at apply.
        rca_drive_commit [list $fd_b $fd_r1 $fd_r2 $fd_l] $idx_f1 0 5000
        after 100
        rca_drain_and_ack $fd_b 1
        assert_equal $idx_f1 [CI 0 cluster_raft_commit_index]
        assert_equal $skipped_before [count_log_message 0 "Proposal rejected at apply"]

        # --- Sub-case 2: uncommitted SLOT_CHANGE to L followed by NODE_FORGET L ---
        set commit_before [CI 0 cluster_raft_commit_index]
        set idx_slot [expr {$commit_before + 1}]

        # Assign slot 0 to learner L (uncommitted; B silent).
        rca_send $in_l "PROPOSE SLOT_CHANGE - 0 $l_id 0 0"
        rca_ack_up_to $fd_l $idx_slot 5000
        assert_equal $commit_before [CI 0 cluster_raft_commit_index]

        # Propose NODE_FORGET L while SLOT_CHANGE is uncommitted.
        # In S_p, L already owns slot 0 -> must be REJECTed before append!
        rca_send $in_l "PROPOSE NODE_FORGET $l_id 0"
        set rej [rca_try_recv_matching $in_l "REJECT *" 1000]
        assert_match "REJECT *" $rej

        # Commit SLOT_CHANGE and confirm L still exists with slot 0 and zero apply rejections.
        rca_drive_commit [list $fd_b $fd_r1 $fd_r2 $fd_l] $idx_slot 0 5000
        after 100
        rca_drain_and_ack $fd_b 1
        assert_equal $idx_slot [CI 0 cluster_raft_commit_index]
        assert_equal 1 [raft_node_visible [srv 0 client] $l_id]
        assert_equal $skipped_before [count_log_message 0 "Proposal rejected at apply"]

        foreach fd [list $fd_b $fd_r1 $fd_r2 $fd_l $in_r1 $in_r2 $in_l] {close $fd}
    }
}

# ==========================================================================
# Step 2(1): Truncation of uncommitted voter change rolls back effective voters
# ==========================================================================
test "Raft config-append: truncation of uncommitted DEL_VOTER restores voting" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 1000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set n_id [R 0 CLUSTER MYID]
        set n_addr "127.0.0.1:[srv 0 port]@$cport,,tls-port=0,shard-id=[string repeat 1 40]"
        set a_id [string repeat "a" 40]
        set a_addr "127.0.0.1:9911@19911,,tls-port=0,shard-id=[string repeat 2 40]"
        set b_id [string repeat "b" 40]
        set b_addr "127.0.0.1:9912@19912,,tls-port=0,shard-id=[string repeat 3 40]"

        set fd_a [rca_connect_fake_node 127.0.0.1 $cport $a_id $a_addr]
        rca_send $fd_a "MEET cluster"
        assert_match "ADD_ME*" [rca_recv $fd_a]

        # Seed {A, N} as voters + B as learner (all committed).
        set base_idx [rca_seed_cluster $fd_a $a_id $a_addr [list \
            [list $n_id $n_addr 1] \
            [list $b_id $b_addr 0]]]
        assert_equal 2 [CI 0 cluster_size]

        # Append uncommitted DEL_VOTER N at base_idx+1.
        set uncomm_idx [expr {$base_idx + 1}]
        rca_send $fd_a "AE $a_id 1 $base_idx 1 $base_idx 1\n1 DEL_VOTER $n_id"
        assert_match "AE_ACK 1 1 $uncomm_idx *" [rca_recv_until $fd_a "AE_ACK *"]
        assert_equal $base_idx [CI 0 cluster_raft_last_applied]

        # Wait for leader lease to expire. N is demoted in projected state S_p,
        # so N MUST deny PRE_VOTE_REQ and VOTE_REQ from A.
        after 1100
        rca_send $fd_a "PRE_VOTE_REQ $a_id 2 $uncomm_idx 1"
        assert_match "PRE_VOTE * 0" [rca_recv_until $fd_a "PRE_VOTE *"]
        rca_send $fd_a "VOTE_REQ $a_id 2 $uncomm_idx 1"
        assert_match "VOTE 2 0" [rca_recv_until $fd_a "VOTE *"]

        # Truncate uncommitted DEL_VOTER N by overwriting uncomm_idx in term 3.
        rca_send $fd_a "AE $a_id 3 $base_idx 1 $base_idx 1\n3 NOOP "
        assert_match "AE_ACK 3 1 $uncomm_idx *" [rca_recv_until $fd_a "AE_ACK *"]

        # Wait for leader lease to expire. Truncation recomputed S_p, so N is a
        # voter again and MUST grant PRE_VOTE_REQ and VOTE_REQ in term 4.
        after 1100
        rca_send $fd_a "PRE_VOTE_REQ $a_id 4 $uncomm_idx 3"
        assert_match "PRE_VOTE 4 1" [rca_recv_until $fd_a "PRE_VOTE *"]
        rca_send $fd_a "VOTE_REQ $a_id 4 $uncomm_idx 3"
        assert_match "VOTE 4 1" [rca_recv_until $fd_a "VOTE *"]

        close $fd_a
    }
}

test "Raft config-append: truncation of uncommitted ADD_VOTER rolls back voter status" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 1000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set n_id [R 0 CLUSTER MYID]
        set n_addr "127.0.0.1:[srv 0 port]@$cport,,tls-port=0,shard-id=[string repeat 1 40]"
        set a_id [string repeat "a" 40]
        set a_addr "127.0.0.1:9921@19921,,tls-port=0,shard-id=[string repeat 2 40]"
        set b_id [string repeat "b" 40]
        set b_addr "127.0.0.1:9922@19922,,tls-port=0,shard-id=[string repeat 3 40]"

        set fd_a [rca_connect_fake_node 127.0.0.1 $cport $a_id $a_addr]
        rca_send $fd_a "MEET cluster"
        assert_match "ADD_ME*" [rca_recv $fd_a]

        set base_idx [rca_seed_cluster $fd_a $a_id $a_addr [list \
            [list $n_id $n_addr 1] \
            [list $b_id $b_addr 0]]]

        set fd_b [rca_connect_fake_node 127.0.0.1 $cport $b_id $b_addr]

        # Append uncommitted ADD_VOTER B at base_idx+1.
        set uncomm_idx [expr {$base_idx + 1}]
        rca_send $fd_a "AE $a_id 1 $base_idx 1 $base_idx 1\n1 ADD_VOTER $b_id"
        assert_match "AE_ACK 1 1 $uncomm_idx *" [rca_recv_until $fd_a "AE_ACK *"]

        # Wait past leader lease: B is a voter in S_p, so N MUST grant PRE_VOTE to B.
        after 1100
        rca_send $fd_b "PRE_VOTE_REQ $b_id 2 $uncomm_idx 1"
        assert_match "PRE_VOTE 2 1" [rca_recv_until $fd_b "PRE_VOTE *"]

        # Truncate uncommitted ADD_VOTER B in term 2 with a NOOP.
        rca_send $fd_a "AE $a_id 2 $base_idx 1 $base_idx 1\n2 NOOP "
        assert_match "AE_ACK 2 1 $uncomm_idx *" [rca_recv_until $fd_a "AE_ACK *"]

        # Wait past leader lease: B is a learner again in S_p, so N MUST deny B.
        after 1100
        rca_send $fd_b "PRE_VOTE_REQ $b_id 3 $uncomm_idx 2"
        assert_match "PRE_VOTE 2 0" [rca_recv_until $fd_b "PRE_VOTE *"]
        rca_send $fd_b "VOTE_REQ $b_id 3 $uncomm_idx 2"
        assert_match "VOTE 3 0" [rca_recv_until $fd_b "VOTE *"]

        close $fd_b
        close $fd_a
    }
}

# ==========================================================================
# Step 2(2): Restart rebuilds the projected voter set from the persisted tail
# ==========================================================================
test "Raft config-append: restart rebuilds projected voter set from persisted tail" {
    # Sub-case A: uncommitted ADD_VOTER B in persisted tail survives crash/restart.
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 1000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set n_id [R 0 CLUSTER MYID]
        set n_addr "127.0.0.1:[srv 0 port]@$cport,,tls-port=0,shard-id=[string repeat 1 40]"
        set a_id [string repeat "a" 40]
        set a_addr "127.0.0.1:9931@19931,,tls-port=0,shard-id=[string repeat 2 40]"
        set b_id [string repeat "b" 40]
        set b_addr "127.0.0.1:9932@19932,,tls-port=0,shard-id=[string repeat 3 40]"

        set fd_a [rca_connect_fake_node 127.0.0.1 $cport $a_id $a_addr]
        rca_send $fd_a "MEET cluster"
        assert_match "ADD_ME*" [rca_recv $fd_a]

        set base_idx [rca_seed_cluster $fd_a $a_id $a_addr [list \
            [list $n_id $n_addr 1] \
            [list $b_id $b_addr 0]]]

        # Persist uncommitted ADD_VOTER B at base_idx+1 (last_applied stays base_idx).
        set uncomm_idx [expr {$base_idx + 1}]
        rca_send $fd_a "AE $a_id 1 $base_idx 1 $base_idx 1\n1 ADD_VOTER $b_id"
        assert_match "AE_ACK 1 1 $uncomm_idx *" [rca_recv_until $fd_a "AE_ACK *"]
        assert_equal $base_idx [CI 0 cluster_raft_last_applied]
        close $fd_a

        # Crash and restart N.
        exec kill -9 [srv 0 pid]
        restart_server 0 true false
        assert_equal $base_idx [CI 0 cluster_raft_last_applied]

        # Wait past lease; N must remember from the persisted tail that B is a voter.
        after 1100
        set fd_b [rca_connect_fake_node 127.0.0.1 $cport $b_id $b_addr]
        rca_send $fd_b "PRE_VOTE_REQ $b_id 2 $uncomm_idx 1"
        assert_match "PRE_VOTE 2 1" [rca_recv_until $fd_b "PRE_VOTE *"]
        close $fd_b
    }

    # Sub-case B: uncommitted DEL_VOTER N in persisted tail survives crash/restart.
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 1000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set n_id [R 0 CLUSTER MYID]
        set n_addr "127.0.0.1:[srv 0 port]@$cport,,tls-port=0,shard-id=[string repeat 1 40]"
        set a_id [string repeat "a" 40]
        set a_addr "127.0.0.1:9933@19933,,tls-port=0,shard-id=[string repeat 2 40]"
        set b_id [string repeat "b" 40]
        set b_addr "127.0.0.1:9934@19934,,tls-port=0,shard-id=[string repeat 3 40]"

        set fd_a [rca_connect_fake_node 127.0.0.1 $cport $a_id $a_addr]
        rca_send $fd_a "MEET cluster"
        assert_match "ADD_ME*" [rca_recv $fd_a]

        set base_idx [rca_seed_cluster $fd_a $a_id $a_addr [list \
            [list $n_id $n_addr 1] \
            [list $b_id $b_addr 0]]]

        set uncomm_idx [expr {$base_idx + 1}]
        rca_send $fd_a "AE $a_id 1 $base_idx 1 $base_idx 1\n1 DEL_VOTER $n_id"
        assert_match "AE_ACK 1 1 $uncomm_idx *" [rca_recv_until $fd_a "AE_ACK *"]
        assert_equal $base_idx [CI 0 cluster_raft_last_applied]
        close $fd_a

        # Crash and restart N.
        exec kill -9 [srv 0 pid]
        restart_server 0 true false
        assert_equal PONG [R 0 PING]
        assert_equal $base_idx [CI 0 cluster_raft_last_applied]

        # Wait past lease; N must remember from the persisted tail that N is demoted.
        after 1100
        set fd_a [rca_connect_fake_node 127.0.0.1 $cport $a_id $a_addr]
        rca_send $fd_a "PRE_VOTE_REQ $a_id 2 $uncomm_idx 1"
        assert_match "PRE_VOTE * 0" [rca_recv_until $fd_a "PRE_VOTE *"]
        rca_send $fd_a "VOTE_REQ $a_id 2 $uncomm_idx 1"
        assert_match "VOTE 2 0" [rca_recv_until $fd_a "VOTE *"]
        close $fd_a
    }
}

# ==========================================================================
# Step 2(3): At most one uncommitted voter change
# ==========================================================================
test "Raft config-append: at most one uncommitted voter change allowed" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set b_id [string repeat "b" 40]
        set c_id [string repeat "c" 40]
        set d_id [string repeat "d" 40]

        lassign [rca_join_fake_learner $b_id [string repeat "2" 40]] fd_b b_addr
        rca_promote_fake_voter $b_id [list $fd_b]
        lassign [rca_join_fake_learner $c_id [string repeat "3" 40] [list $fd_b]] fd_c c_addr
        lassign [rca_join_fake_learner $d_id [string repeat "4" 40] [list $fd_b $fd_c]] fd_d d_addr

        set in_d [rca_connect_fake_node 127.0.0.1 $cport $d_id $d_addr]
        set base_commit [CI 0 cluster_raft_commit_index]
        set idx_c [expr {$base_commit + 1}]

        # Propose ADD_VOTER C while B does not ack -> stays uncommitted.
        set rd_c [valkey_deferring_client]
        $rd_c CLUSTER ADDVOTER $c_id
        rca_ack_all_up_to [list $fd_c $fd_d] $idx_c 5000
        assert_equal $base_commit [CI 0 cluster_raft_commit_index]
        set entries_after_c [CI 0 cluster_raft_log_entries]

        # A second voter change (ADD_VOTER D or DEL_VOTER B) must be rejected immediately.
        set err ""
        assert_equal 1 [catch {R 0 CLUSTER ADDVOTER $d_id} err]
        assert_no_match "*TIMEOUT*" $err
        assert_equal $entries_after_c [CI 0 cluster_raft_log_entries]

        set err ""
        assert_equal 1 [catch {R 0 CLUSTER DELVOTER $b_id} err]
        assert_no_match "*TIMEOUT*" $err
        assert_equal $entries_after_c [CI 0 cluster_raft_log_entries]

        # Wire PROPOSE ADD_VOTER D must also be rejected with REJECT.
        rca_send $in_d "PROPOSE ADD_VOTER $d_id"
        assert_match "REJECT *" [rca_try_recv_matching $in_d "REJECT *" 1000]
        assert_equal $entries_after_c [CI 0 cluster_raft_log_entries]

        # Commit ADD_VOTER C by letting B ack.
        rca_drive_commit [list $fd_b $fd_c $fd_d] $idx_c 0 5000
        assert_equal "OK" [$rd_c read]
        $rd_c close
        assert_equal 3 [CI 0 cluster_size]

        # Now ADD_VOTER D is allowed once ADD_VOTER C committed.
        rca_promote_fake_voter $d_id [list $fd_b $fd_c $fd_d]
        assert_equal 4 [CI 0 cluster_size]

        # Now test uncommitted DEL_VOTER blocking a second DEL_VOTER.
        # In 4-voter {A, B, C, D}, demoting D makes effective voters {A, B, C} (quorum=2).
        # Hold back B and C so DEL_VOTER D stays uncommitted.
        set base_commit [CI 0 cluster_raft_commit_index]
        set idx_del_d [expr {$base_commit + 1}]
        set rd_del_d [valkey_deferring_client]
        $rd_del_d CLUSTER DELVOTER $d_id
        rca_ack_up_to $fd_d $idx_del_d 5000
        assert_equal $base_commit [CI 0 cluster_raft_commit_index]
        set entries_after_del_d [CI 0 cluster_raft_log_entries]

        set err ""
        assert_equal 1 [catch {R 0 CLUSTER DELVOTER $c_id} err]
        assert_no_match "*TIMEOUT*" $err
        assert_equal $entries_after_del_d [CI 0 cluster_raft_log_entries]

        # Commit DEL_VOTER D by letting B ack ({A, B} = quorum 2 of {A, B, C}).
        rca_drive_commit [list $fd_b $fd_c $fd_d] $idx_del_d 0 5000
        assert_equal "OK" [$rd_del_d read]
        $rd_del_d close
        assert_equal 3 [CI 0 cluster_size]

        foreach fd [list $fd_b $fd_c $fd_d $in_d] {close $fd}
    }
}

# ==========================================================================
# Step 2(4): New leader cannot propose voter change before committing own term
# ==========================================================================
test "Raft config-append: new leader must commit own-term entry before voter change" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 1000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set n_id [R 0 CLUSTER MYID]
        set n_addr "127.0.0.1:[srv 0 port]@$cport,,tls-port=0,shard-id=[string repeat 1 40]"
        set a_id [string repeat "a" 40]
        set b_id [string repeat "b" 40]
        set c_id [string repeat "c" 40]

        set listen_a [rca_listen a_cport]
        set listen_b [rca_listen b_cport]
        set listen_c [rca_listen c_cport]
        set a_addr "127.0.0.1:[expr {$a_cport - 10000}]@$a_cport,,tls-port=0,shard-id=[string repeat 2 40]"
        set b_addr "127.0.0.1:[expr {$b_cport - 10000}]@$b_cport,,tls-port=0,shard-id=[string repeat 3 40]"
        set c_addr "127.0.0.1:[expr {$c_cport - 10000}]@$c_cport,,tls-port=0,shard-id=[string repeat 4 40]"

        # A forms 3-voter cluster {A, N, B} + learner C.
        set fd_a [rca_connect_fake_node 127.0.0.1 $cport $a_id $a_addr]
        rca_send $fd_a "MEET cluster"
        assert_match "ADD_ME*" [rca_recv $fd_a]

        set base_idx [rca_seed_cluster $fd_a $a_id $a_addr [list \
            [list $n_id $n_addr 1] \
            [list $b_id $b_addr 1] \
            [list $c_id $c_addr 0]]]
        assert_equal 3 [CI 0 cluster_size]

        set out_a [rca_accept $listen_a]
        set out_b [rca_accept $listen_b]
        set out_c [rca_accept $listen_c]
        assert_match "HELLO *" [rca_recv $out_a]
        rca_send $out_a "HI $a_id $a_addr"
        assert_match "HELLO *" [rca_recv $out_b]
        rca_send $out_b "HI $b_id $b_addr"
        assert_match "HELLO *" [rca_recv $out_c]
        rca_send $out_c "HI $c_id $c_addr"

        # A goes silent; B elects N in term 2.
        set pv [rca_recv_until $out_b "PRE_VOTE_REQ $n_id 2 $base_idx 1" 5000]
        rca_send $out_b "PRE_VOTE 2 1"
        set vr [rca_recv_until $out_b "VOTE_REQ $n_id 2 $base_idx 1" 5000]
        rca_send $out_b "VOTE 2 1"

        wait_for_condition 50 50 {[CI 0 cluster_raft_role] eq "leader"} else {
            fail "N did not become leader in term 2"
        }
        assert_equal 2 [CI 0 cluster_raft_current_term]

        # N appended its term-2 NOOP at noop_idx, still uncommitted because
        # neither A nor B has acked it yet.
        set noop_idx [expr {$base_idx + 1}]
        assert_equal $base_idx [CI 0 cluster_raft_commit_index]

        # Let learner C ack noop_idx so C is fully caught up (ADD_VOTER C won't
        # be rejected merely for lag).
        rca_ack_up_to $out_c $noop_idx 5000
        assert_equal $base_idx [CI 0 cluster_raft_commit_index]
        set entries_at_noop [CI 0 cluster_raft_log_entries]

        # Before term-2 NOOP commits, N MUST reject voter changes!
        set err ""
        assert_equal 1 [catch {R 0 CLUSTER ADDVOTER $c_id} err]
        assert_no_match "*TIMEOUT*" $err
        assert_equal $entries_at_noop [CI 0 cluster_raft_log_entries]

        set err ""
        assert_equal 1 [catch {R 0 CLUSTER DELVOTER $b_id} err]
        assert_no_match "*TIMEOUT*" $err
        assert_equal $entries_at_noop [CI 0 cluster_raft_log_entries]

        set in_b [rca_connect_fake_node 127.0.0.1 $cport $b_id $b_addr]
        rca_send $in_b "PROPOSE DEL_VOTER $b_id"
        assert_match "REJECT *" [rca_try_recv_matching $in_b "REJECT *" 1000]
        assert_equal $entries_at_noop [CI 0 cluster_raft_log_entries]

        # Now B acks noop_idx -> N commits its term-2 NOOP!
        rca_drive_commit [list $out_b $out_c] $noop_idx 0 5000
        assert_equal $noop_idx [CI 0 cluster_raft_commit_index]

        # Now voter changes are allowed. Demote B (effective voters {A, N},
        # so A acking commits DEL_VOTER B).
        set del_idx [expr {$noop_idx + 1}]
        set rd [valkey_deferring_client]
        $rd CLUSTER DELVOTER $b_id
        rca_drive_commit [list $out_a $out_b $out_c] $del_idx 0 5000
        assert_equal "OK" [$rd read]
        $rd close
        assert_equal 2 [CI 0 cluster_size]

        foreach fd [list $fd_a $out_a $out_b $out_c $in_b] {close $fd}
    }
}

# ==========================================================================
# Step 2(5): NODE_JOIN ... voter rejected except empty-log bootstrap self-join
# ==========================================================================
test "Raft config-append: NODE_JOIN voter rejected except bootstrap self-join" {
    # Sub-case A: fresh singleton leader (empty log) rejects PROPOSE NODE_JOIN <other> voter.
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set x_id [string repeat "x" 40]
        set x_addr "127.0.0.1:9941@19941,,tls-port=0,shard-id=[string repeat 5 40]"

        assert_equal 0 [CI 0 cluster_raft_last_applied]
        assert_equal 0 [CI 0 cluster_raft_log_entries]

        set in_x [rca_connect_fake_node 127.0.0.1 $cport $x_id $x_addr]
        rca_send $in_x "PROPOSE NODE_JOIN $x_id $x_addr voter"
        assert_match "REJECT *" [rca_try_recv_matching $in_x "REJECT *" 1000]
        assert_equal 0 [CI 0 cluster_raft_log_entries]
        assert_equal 0 [CI 0 cluster_raft_last_applied]
        close $in_x
    }

    # Sub-case B: after bootstrap (non-empty log), PROPOSE NODE_JOIN <other> voter
    # is rejected, while learner is accepted.
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000}} {
        set a_id [R 0 CLUSTER MYID]
        set cport [expr {[srv 0 port] + 10000}]
        set b_id [string repeat "b" 40]
        set c_id [string repeat "c" 40]
        set c_addr "127.0.0.1:9942@19942,,tls-port=0,shard-id=[string repeat 6 40]"

        # Join fake learner B and inspect bootstrap entries:
        # index 1 must be self-join voter, index 2 must be B as learner.
        set bcport 0
        set fd_b [rca_listen_and_accept bcport 5000 {
            set bport [expr {$bcport - 10000}]
            set b_addr "127.0.0.1:${bport}@${bcport},,tls-port=0,shard-id=[string repeat 2 40]"
            set meet_c [valkey_deferring_client]
            $meet_c CLUSTER MEET 127.0.0.1 $bport
        }]
        assert_match "HELLO *" [rca_recv $fd_b 5000]
        assert_match "MEET *" [rca_recv $fd_b 5000]
        rca_send $fd_b "HI $b_id $b_addr"
        rca_send $fd_b "ADD_ME"
        set first_ae [rca_recv_until $fd_b "AE *NODE_JOIN*" 5000]
        assert_match "*NODE_JOIN $a_id * voter*" $first_ae
        assert_match "*NODE_JOIN $b_id * learner*" $first_ae
        rca_reply_ae_ack $fd_b $first_ae 0
        assert_equal "OK" [$meet_c read]
        $meet_c close

        # Now log is non-empty. PROPOSE NODE_JOIN C voter MUST be rejected.
        set commit_before [CI 0 cluster_raft_commit_index]
        set in_b [rca_connect_fake_node 127.0.0.1 $cport $b_id $b_addr]
        rca_send $in_b "PROPOSE NODE_JOIN $c_id $c_addr voter"
        assert_match "REJECT *" [rca_try_recv_matching $in_b "REJECT *" 1000]
        assert_equal $commit_before [CI 0 cluster_raft_commit_index]
        assert_equal 0 [raft_node_visible [srv 0 client] $c_id]

        # PROPOSE NODE_JOIN C learner IS accepted.
        rca_send $in_b "PROPOSE NODE_JOIN $c_id $c_addr learner"
        rca_drive_commit [list $fd_b] [expr {$commit_before + 1}] 0 5000
        assert_equal 1 [raft_node_visible [srv 0 client] $c_id]
        assert_equal 1 [raft_node_has_flag [srv 0 client] $c_id learner]
        assert_equal 1 [CI 0 cluster_size]

        close $in_b
        close $fd_b
    }
}

# ==========================================================================
# Step 2(6): NODE_FORGET of a voter rejected
# ==========================================================================
test "Raft config-append: NODE_FORGET of a voter is rejected until demoted" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set b_id [string repeat "b" 40]
        set c_id [string repeat "c" 40]

        # Form 3-voter cluster {A, B, C}.
        lassign [rca_join_fake_learner $b_id [string repeat "2" 40]] fd_b b_addr
        rca_promote_fake_voter $b_id [list $fd_b]
        lassign [rca_join_fake_learner $c_id [string repeat "3" 40] [list $fd_b]] fd_c c_addr
        rca_promote_fake_voter $c_id [list $fd_b $fd_c]
        assert_equal 3 [CI 0 cluster_size]

        # Direct wire PROPOSE NODE_FORGET for voter B MUST be rejected.
        set in_c [rca_connect_fake_node 127.0.0.1 $cport $c_id $c_addr]
        set commit_before [CI 0 cluster_raft_commit_index]
        rca_send $in_c "PROPOSE NODE_FORGET $b_id 0"
        assert_match "REJECT *" [rca_try_recv_matching $in_c "REJECT *" 1000]
        assert_equal $commit_before [CI 0 cluster_raft_commit_index]
        assert_equal 1 [raft_node_visible [srv 0 client] $b_id]
        assert_equal 3 [CI 0 cluster_size]

        # Demote B to learner first.
        set del_idx [expr {$commit_before + 1}]
        set rd [valkey_deferring_client]
        $rd CLUSTER DELVOTER $b_id
        rca_drive_commit [list $fd_b $fd_c] $del_idx 0 5000
        assert_equal "OK" [$rd read]
        $rd close
        assert_equal 2 [CI 0 cluster_size]
        assert_equal 1 [raft_node_has_flag [srv 0 client] $b_id learner]

        # Now PROPOSE NODE_FORGET for learner B MUST succeed.
        set forget_idx [expr {$del_idx + 1}]
        rca_send $in_c "PROPOSE NODE_FORGET $b_id 0"
        rca_drive_commit [list $fd_c] $forget_idx 0 5000
        assert_equal 0 [raft_node_visible [srv 0 client] $b_id]
        assert_equal 2 [CI 0 cluster_size]

        foreach fd [list $fd_b $fd_c $in_c] {close $fd}
    }
}

# ==========================================================================
# Step 2(7): Leader removed from effective voters does not count self ack
#            and steps down once DEL_VOTER(myself) commits
# ==========================================================================
test "Raft config-append: leader demoting itself does not count self ack and steps down" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000}} {
        set a_id [R 0 CLUSTER MYID]
        set b_id [string repeat "b" 40]
        set c_id [string repeat "c" 40]

        # Form 3-voter cluster {A, B, C} led by A.
        lassign [rca_join_fake_learner $b_id [string repeat "2" 40]] fd_b b_addr
        rca_promote_fake_voter $b_id [list $fd_b]
        lassign [rca_join_fake_learner $c_id [string repeat "3" 40] [list $fd_b]] fd_c c_addr
        rca_promote_fake_voter $c_id [list $fd_b $fd_c]
        assert_equal 3 [CI 0 cluster_size]

        set commit_before [CI 0 cluster_raft_commit_index]
        set del_idx [expr {$commit_before + 1}]

        # Demote the leader A itself. Effective voters become {B, C} (quorum=2).
        set rd [valkey_deferring_client]
        $rd CLUSTER DELVOTER $a_id

        # Wait for A to replicate DEL_VOTER A to B, and have ONLY B ack it.
        set ae_b [rca_try_recv_matching $fd_b "AE *DEL_VOTER $a_id*" 2000]
        assert_match "AE *DEL_VOTER $a_id*" $ae_b
        rca_reply_ae_ack $fd_b $ae_b 0

        # A is NOT in effective voters {B, C}, so A+B must NOT commit (only 1/2
        # effective voters acked).
        after 300
        assert_equal $commit_before [CI 0 cluster_raft_commit_index] \
            "leader counted its own ack after DEL_VOTER(myself)"
        assert_equal "leader" [CI 0 cluster_raft_role]

        # Now C also acks DEL_VOTER A -> 2/2 effective voters {B, C} -> commits
        # and A steps down to learner!
        rca_drive_commit [list $fd_b $fd_c] $del_idx 0 5000
        assert_equal "OK" [$rd read]
        $rd close

        wait_for_condition 50 50 {
            [CI 0 cluster_raft_role] eq "learner" &&
            [CI 0 cluster_size] == 2 &&
            [raft_node_has_flag [srv 0 client] $a_id learner]
        } else {
            fail "leader did not step down to learner after DEL_VOTER(myself): role=[CI 0 cluster_raft_role] size=[CI 0 cluster_size]"
        }

        close $fd_b
        close $fd_c
    }
}

# ==========================================================================
# Step 2(8): CLUSTER FORGET of a voter chains DEL_VOTER then NODE_FORGET
# ==========================================================================
test "Raft config-append: CLUSTER FORGET of a voter chains DEL_VOTER then NODE_FORGET" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 5000}} {
        set b_id [string repeat "b" 40]
        set c_id [string repeat "c" 40]

        lassign [rca_join_fake_learner $b_id [string repeat "2" 40]] fd_b b_addr
        rca_promote_fake_voter $b_id [list $fd_b]
        lassign [rca_join_fake_learner $c_id [string repeat "3" 40] [list $fd_b]] fd_c c_addr
        rca_promote_fake_voter $c_id [list $fd_b $fd_c]
        assert_equal 3 [CI 0 cluster_size]

        set commit_before [CI 0 cluster_raft_commit_index]
        set del_idx [expr {$commit_before + 1}]

        # Run CLUSTER FORGET on voter B.
        set rd [valkey_deferring_client]
        $rd CLUSTER FORGET $b_id

        # First entry replicated MUST be DEL_VOTER B (NOT NODE_FORGET B).
        set ae1 [rca_try_recv_matching $fd_c "AE *DEL_VOTER $b_id*" 2000]
        assert_match "*DEL_VOTER $b_id*" $ae1
        assert_no_match "*NODE_FORGET $b_id*" $ae1

        # Ack DEL_VOTER B from C -> effective voters {A, C} commit DEL_VOTER B.
        rca_reply_ae_ack $fd_c $ae1 0
        rca_drive_commit [list $fd_c] $del_idx 0 5000

        # Next entry replicated MUST be NODE_FORGET B.
        set forget_idx [expr {$del_idx + 1}]
        set ae2 [rca_try_recv_matching $fd_c "AE *NODE_FORGET $b_id*" 5000]
        assert_match "*NODE_FORGET $b_id*" $ae2
        rca_reply_ae_ack $fd_c $ae2 0
        rca_drive_commit [list $fd_c] $forget_idx 0 5000

        assert_equal "OK" [$rd read]
        $rd close
        assert_equal 0 [raft_node_visible [srv 0 client] $b_id]
        assert_equal 2 [CI 0 cluster_size]

        close $fd_b
        close $fd_c
    }
}

# ==========================================================================
# Step 2(9): INSTALL_SNAPSHOT rebuilds projected voter set
# ==========================================================================
test "Raft config-append: INSTALL_SNAPSHOT rebuilds projected voter set" {
    start_server {overrides {cluster-enabled yes cluster-protocol raft cluster-node-timeout 1000}} {
        set cport [expr {[srv 0 port] + 10000}]
        set n_id [R 0 CLUSTER MYID]
        set n_addr "127.0.0.1:[srv 0 port]@$cport,,tls-port=0,shard-id=[string repeat 1 40]"
        set a_id [string repeat "a" 40]
        set a_addr "127.0.0.1:9951@19951,,tls-port=0,shard-id=[string repeat 2 40]"
        set b_id [string repeat "b" 40]
        set b_addr "127.0.0.1:9952@19952,,tls-port=0,shard-id=[string repeat 3 40]"

        set fd_a [rca_connect_fake_node 127.0.0.1 $cport $a_id $a_addr]
        rca_send $fd_a "MEET cluster"
        assert_match "ADD_ME*" [rca_recv $fd_a]

        set base_idx [rca_seed_cluster $fd_a $a_id $a_addr [list \
            [list $n_id $n_addr 1] \
            [list $b_id $b_addr 0]]]

        # Uncommitted ADD_VOTER B makes B a voter in S_p.
        set uncomm_idx [expr {$base_idx + 1}]
        rca_send $fd_a "AE $a_id 1 $base_idx 1 $base_idx 1\n1 ADD_VOTER $b_id"
        assert_match "AE_ACK 1 1 $uncomm_idx *" [rca_recv_until $fd_a "AE_ACK *"]

        set fd_b [rca_connect_fake_node 127.0.0.1 $cport $b_id $b_addr]
        after 1100
        rca_send $fd_b "PRE_VOTE_REQ $b_id 2 $uncomm_idx 1"
        assert_match "PRE_VOTE 2 1" [rca_recv_until $fd_b "PRE_VOTE *"]

        # Leader A in term 2 installs a snapshot at index 10 where B is a learner.
        # This replaces the log and MUST rebuild S_p so B is no longer a voter.
        set snap "INSTALL_SNAPSHOT $a_id 2 10 2"
        append snap "\n$a_id $a_addr master - 0 0 1 connected 0-16383"
        append snap "\n$n_id $n_addr master - 0 0 1 connected"
        append snap "\n$b_id $b_addr master,learner - 0 0 1 connected"
        rca_send $fd_a $snap
        assert_match "AE_ACK 2 1 10 *" [rca_recv_until $fd_a "AE_ACK *"]
        assert_equal 10 [CI 0 cluster_raft_last_applied]
        assert_equal 2 [CI 0 cluster_size]

        after 1100
        rca_send $fd_b "PRE_VOTE_REQ $b_id 3 10 2"
        assert_match "PRE_VOTE 2 0" [rca_recv_until $fd_b "PRE_VOTE *"]

        close $fd_b
        close $fd_a
    }
}

} ;# tags
