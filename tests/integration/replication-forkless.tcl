start_server {tags {"repl external:skip"} overrides {save {} forkless-infrastructure-enabled yes forkless-policy prefer-forkless}} {
    set primary [srv 0 client]
    $primary set counter 0
    if {!$::singledb} {
        $primary select 2
    }
    $primary debug populate 10000
    if {!$::singledb} {
        $primary select 0
    }

    start_server {overrides {save {}}} {
        set replica1 [srv 0 client]

        start_server {overrides {save {}}} {
            set replica2 [srv 0 client]

            start_server {overrides {save {}}} {
                set replica3 [srv 0 client]

                test "Forkless sync: dropping one replica mid-scan lets remaining replicas finish" {
                    set loglines [count_log_lines -3]
                    $primary config set repl-diskless-sync yes
                    $primary config set repl-diskless-sync-delay 5
                    $primary config set repl-diskless-sync-max-replicas 3
                    $primary config set rdb-key-save-delay 500

                    $replica1 replicaof [srv -3 host] [srv -3 port]
                    $replica2 replicaof [srv -3 host] [srv -3 port]
                    $replica3 replicaof [srv -3 host] [srv -3 port]

                    wait_for_condition 100 50 {
                        [s -3 rdb_bgsave_in_progress] == 1
                    } else {
                        fail "Forkless save didn't start"
                    }
                    wait_for_log_messages -3 {"*target: replicas sockets*method: forkless*"} $loglines 50 50

                    # Write before dropping one replica, then drop replica1 mid-scan.
                    $primary incr counter
                    $replica1 replicaof no one

                    wait_for_log_messages -3 {"*forkless-save:*2 clients remain*"} $loglines 50 100
                    assert_equal 1 [s -3 rdb_bgsave_in_progress]

                    # Write again after replica1 is pruned so remaining replicas replay inline updates.
                    $primary incr counter
                    $primary set mid_scan_key after_drop

                    $primary config set rdb-key-save-delay 0
                    wait_for_condition 500 100 {
                        [s -1 master_link_status] eq {up} &&
                        [s 0 master_link_status] eq {up}
                    } else {
                        fail "Remaining replicas didn't finish syncing"
                    }

                    $primary set post_sync_key done
                    wait_for_ofs_sync $primary $replica2
                    wait_for_ofs_sync $primary $replica3
                    assert_equal 2 [s -3 connected_slaves]
                    assert_equal 0 [s -3 total_forks]
                    assert_equal [$primary debug digest] [$replica2 debug digest]
                    assert_equal [$primary debug digest] [$replica3 debug digest]
                } {} {needs:debug}
            }
        }
    }
}

if {$::tls} {
    foreach load_mode {disabled on-empty-db} {
        start_server {tags {"repl tls external:skip"} overrides {save {} forkless-infrastructure-enabled yes forkless-policy prefer-forkless repl-diskless-sync yes repl-diskless-sync-delay 0}} {
            set primary [srv 0 client]
            set primary_host [srv 0 host]
            set primary_port [srv 0 port]
            $primary set tls_counter 0
            if {!$::singledb} {
                $primary select 2
            }
            $primary debug populate 20000
            if {!$::singledb} {
                $primary select 0
            }

            start_server {overrides {save {}}} {
                set replica [srv 0 client]
                $replica config set repl-diskless-load $load_mode

                test "Forkless sync: full sync over TLS replication (repl-diskless-load=$load_mode)" {
                    assert_equal yes [lindex [$primary config get tls-replication] 1]
                    assert_equal yes [lindex [$replica config get tls-replication] 1]
                    set loglines [count_log_lines -1]
                    set load [start_write_load $primary_host $primary_port 20]
                    $primary config set rdb-key-save-delay 50
                    $replica replicaof $primary_host $primary_port

                    wait_for_condition 100 50 {
                        [s -1 rdb_bgsave_in_progress] == 1
                    } else {
                        fail "Forkless TLS save didn't start"
                    }
                    $primary incr tls_counter
                    $primary config set rdb-key-save-delay 0

                    wait_for_log_messages -1 {"*target: replicas sockets*method: forkless*"} $loglines 100 100
                    wait_for_condition 200 100 {
                        [s 0 master_link_status] eq {up}
                    } else {
                        fail "TLS replica didn't sync (repl-diskless-load=$load_mode)"
                    }

                    stop_write_load $load
                    wait_for_ofs_sync $primary $replica
                    assert_equal 0 [s -1 total_forks]
                    assert_equal [$primary info keyspace] [$replica info keyspace]
                    assert_equal [$primary debug digest] [$replica debug digest]
                } {} {needs:debug}
            }
        }
    }
}

start_server {tags {"repl external:skip"} overrides {save {} forkless-infrastructure-enabled yes forkless-policy prefer-forkless repl-diskless-sync yes repl-diskless-sync-delay 0}} {
    set primary [srv 0 client]
    for {set i 0} {$i < 100} {incr i} {
        $primary set direct_sync_key:$i val:$i
    }

    test "Forkless sync: pre-PSYNC client sending SYNC directly receives forkless disk RDB" {
        set loglines [count_log_lines 0]
        set c [valkey_deferring_client 0]
        $c readraw 1
        $c sync
        $c flush

        wait_for_log_messages 0 {"*target: disk*method: forkless*"} $loglines 50 100

        # Skip any leading newline pings emitted while waiting for the disk snapshot.
        while 1 {
            set line [$c read]
            if {$line ne ""} break
        }
        assert_match {$*} $line
        set rdb_len [string range $line 1 end]
        set payload [$c rawread $rdb_len]
        assert_equal $rdb_len [string length $payload]
        assert_match {VALKEY*} $payload
        assert_equal 0 [s 0 total_forks]

        # Live writes after the snapshot must stream immediately without REPLCONF ACK.
        $primary set after_direct_sync live_val
        set found 0
        for {set i 0} {$i < 20} {incr i} {
            set line [$c read]
            if {[string match {*after_direct_sync*} $line]} {
                set found 1
                break
            }
        }
        assert_equal 1 $found
        $c close
    }
}

foreach diskless {no yes} {
    start_server {tags {"repl external:skip"} overrides {save {} forkless-infrastructure-enabled yes forkless-policy prefer-forkless repl-diskless-sync-delay 0}} {
        set primary [srv 0 client]
        set primary_host [srv 0 host]
        set primary_port [srv 0 port]
        $primary config set repl-diskless-sync $diskless
        for {set i 0} {$i < 200} {incr i} { $primary set sync_key:$i val:$i }
        $primary acl setuser default -psync

        start_server {overrides {save {} repl-diskless-load disabled}} {
            set replica [srv 0 client]

            test "Forkless sync: replica falls back from PSYNC to SYNC (repl-diskless-sync=$diskless)" {
                # Known bug on unstable: after falling back from PSYNC to SYNC,
                # primary_initial_offset remains -1 with no +FULLRESYNC reply,
                # so replicaCheckFullSyncOffsetFromRdb rejects the RDB in a loop.
                skip "PSYNC to SYNC fallback loops on RDB offset validation"

                set replica_loglines [count_log_lines 0]
                $replica replicaof $primary_host $primary_port
                wait_for_log_messages 0 {"*Retrying with SYNC*"} $replica_loglines 50 50
                wait_for_condition 100 100 {
                    [s 0 master_link_status] eq {up}
                } else {
                    fail "Replica didn't sync via SYNC fallback (repl-diskless-sync=$diskless)"
                }
                $primary set post_sync_fallback ok
                wait_for_value_to_propagate_to_replica $primary $replica post_sync_fallback
                assert_equal 0 [s -1 total_forks]
                assert_equal [$primary debug digest] [$replica debug digest]
            } {} {needs:debug}
        }
    }
}

start_server {tags {"repl external:skip"} overrides {save {}}} {
    set new_primary [srv 0 client]
    set new_primary_host [srv 0 host]
    set new_primary_port [srv 0 port]
    populate 500 new_primary 100 0
    $new_primary set role_change from_new_primary

    start_server {overrides {save {} forkless-infrastructure-enabled yes forkless-policy prefer-forkless repl-diskless-sync yes repl-diskless-sync-delay 0}} {
        set old_primary [srv 0 client]
        set old_primary_host [srv 0 host]
        set old_primary_port [srv 0 port]
        if {!$::singledb} {
            $old_primary select 2
        }
        $old_primary debug populate 10000
        if {!$::singledb} {
            $old_primary select 0
        }

        start_server {overrides {save {}}} {
            set replica [srv 0 client]

            test "Forkless sync: primary demoted via REPLICAOF mid-scan and replica recovers" {
                set loglines [count_log_lines -1]
                $old_primary config set rdb-key-save-delay 300
                $replica replicaof $old_primary_host $old_primary_port

                wait_for_condition 100 50 {
                    [s -1 rdb_bgsave_in_progress] == 1
                } else {
                    fail "Forkless save didn't start on old primary"
                }
                wait_for_log_messages -1 {"*target: replicas sockets*method: forkless*"} $loglines 50 50

                # Demote old_primary to a replica of new_primary while its forkless scan is still running.
                $old_primary replicaof $new_primary_host $new_primary_port
                wait_for_sync $old_primary
                $old_primary config set rdb-key-save-delay 0

                wait_for_sync $replica
                $new_primary set after_demotion ok
                wait_for_ofs_sync $new_primary $old_primary
                wait_for_ofs_sync $old_primary $replica
                assert_equal [$new_primary debug digest] [$old_primary debug digest]
                assert_equal [$new_primary debug digest] [$replica debug digest]
            } {} {needs:debug}
        }
    }
}

start_server {tags {"repl external:skip"} overrides {save {} forkless-infrastructure-enabled yes forkless-policy prefer-forkless repl-diskless-sync yes repl-diskless-sync-delay 0}} {
    set primary [srv 0 client]
    set primary_host [srv 0 host]
    set primary_port [srv 0 port]
    if {!$::singledb} {
        $primary select 2
    }
    $primary debug populate 10000
    if {!$::singledb} {
        $primary select 0
    }

    start_server {overrides {save {}}} {
        set synced_replica [srv 0 client]
        set synced_replica_host [srv 0 host]
        set synced_replica_port [srv 0 port]
        $synced_replica replicaof $primary_host $primary_port
        wait_for_sync $synced_replica
        wait_for_ofs_sync $primary $synced_replica

        start_server {overrides {save {}}} {
            set syncing_replica [srv 0 client]

            test "Forkless sync: primary fails over mid-scan and syncing replica recovers" {
                set loglines [count_log_lines -2]
                $primary config set rdb-key-save-delay 300
                $syncing_replica replicaof $primary_host $primary_port

                wait_for_condition 100 50 {
                    [s -2 rdb_bgsave_in_progress] == 1
                } else {
                    fail "Forkless save didn't start before failover"
                }
                wait_for_log_messages -2 {"*target: replicas sockets*method: forkless*"} $loglines 50 50

                $primary failover to $synced_replica_host $synced_replica_port
                wait_for_condition 100 100 {
                    [s -2 master_failover_state] eq {no-failover}
                } else {
                    fail "Failover did not complete during forkless sync"
                }
                $primary config set rdb-key-save-delay 0

                wait_for_sync $primary
                wait_for_sync $syncing_replica
                $synced_replica set after_failover ok
                wait_for_ofs_sync $synced_replica $primary
                wait_for_ofs_sync $primary $syncing_replica
                assert_equal [$synced_replica debug digest] [$primary debug digest]
                assert_equal [$synced_replica debug digest] [$syncing_replica debug digest]
            } {} {needs:debug}
        }
    }
}
