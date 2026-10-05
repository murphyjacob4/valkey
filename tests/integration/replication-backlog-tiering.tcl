# Integration tests for replication backlog tiering (repl_backlog_tier.c).
#
# We make a replica fall behind by SIGSTOP-ing it. Once it falls behind the
# in-memory replication backlog, the primary should keep extending the backlog
# on disk (written and fsynced by a bio thread) and serve the replica from
# there, instead of pinning replication buffer memory for it or dropping it.

proc tier_info {r field} {
    getInfoProperty [$r info replication] repl_backlog_tier_$field
}

proc sync_stat {r field} {
    getInfoProperty [$r info stats] $field
}

# Offset acknowledged by the (only) replica.
proc replica_ack_offset {r} {
    if {[regexp {slave0:[^\r\n]*,offset=(\d+)} [$r info replication] -> offset]} {
        return $offset
    }
    return 0
}

# Write roughly nchunks MB of replication stream, ~1MB per command so the
# primary goes through the event loop (and beforeSleep) between chunks. With
# getack, a REPLCONF GETACK follows every chunk in the stream (via WAIT), so
# the replica acknowledges its progress as it consumes the stream.
proc write_chunks {r nchunks {prefix key} {getack 0}} {
    for {set j 0} {$j < $nchunks} {incr j} {
        $r eval {
            local v = string.rep('x', 1000)
            for i = 1, 1000 do
                redis.call('set', ARGV[1] .. ':' .. i, v)
            end
        } 0 $prefix:$j
        if {$getack} { $r wait 1 1 }
    }
}

proc setup_tiered_replication {primary replica primary_host primary_port} {
    # No holds from earlier tests, and none for the replica re-attaching below.
    $primary config set repl-backlog-tiering-retention 0
    $primary replicaof no one
    $primary flushall
    $primary config set repl-backlog-tiering-enabled yes
    $primary config set repl-backlog-tiering-batch-size 64kb
    $primary config set repl-backlog-tiering-max-size 0
    $primary config set repl-backlog-size 1mb
    # Only a hard limit, so a lagging replica would normally be dropped quickly.
    $primary config set client-output-buffer-limit "replica 8mb 0 0"
    $primary config set repl-timeout 1800
    $replica replicaof no one
    $replica flushall
    $replica config set repl-timeout 1800
    $replica replicaof $primary_host $primary_port
    wait_for_sync $replica
    wait_replica_online $primary
    # Nothing references a tier left over from an earlier test anymore.
    wait_for_condition 50 100 {
        [tier_info $primary active] == 0
    } else {
        fail "tier from an earlier test was not released"
    }
    $primary config set repl-backlog-tiering-retention 60
}

proc wait_tiered {primary replica_pid} {
    wait_for_condition 100 100 {
        [tier_info $primary active] == 1 && [tier_info $primary readers] == 1
    } else {
        resume_process $replica_pid
        fail "lagging replica was not moved to the disk tier: [$primary info replication]"
    }
}

proc assert_in_sync {primary replica} {
    wait_for_sync $replica
    wait_replica_online $primary
    wait_for_ofs_sync $primary $replica
    assert_equal [$primary dbsize] [$replica dbsize]
    assert_equal [$primary debug digest] [$replica debug digest]
}

start_server {tags {"repl external:skip valgrind:skip"}} {
    set replica [srv 0 client]
    set replica_pid [srv 0 pid]
    start_server {} {
        set primary [srv 0 client]
        set primary_host [srv 0 host]
        set primary_port [srv 0 port]

        test {Lagging replica is served from disk instead of pinning memory} {
            setup_tiered_replication $primary $replica $primary_host $primary_port
            set full_syncs [sync_stat $primary sync_full]
            set activations [tier_info $primary activations]
            set tiered [tier_info $primary tiered_replicas]

            pause_process $replica_pid
            # ~20MB of replication stream, well past the replica's hard COB limit.
            write_chunks $primary 20
            wait_tiered $primary $replica_pid

            wait_for_condition 100 100 {
                [tier_info $primary write_in_progress] == 0
            } else {
                resume_process $replica_pid
                fail "tier write did not complete"
            }
            assert {[tier_info $primary size] > 10 * 1024 * 1024}
            assert {[tier_info $primary written_bytes] > 10 * 1024 * 1024}
            # Only the backlog plus at most one in-flight job stays in memory;
            # nothing is pinned for the lagging replica itself.
            assert {[getInfoProperty [$primary info memory] mem_clients_slaves] < 4 * 1024 * 1024}
            assert {[getInfoProperty [$primary info replication] repl_backlog_histlen] < 4 * 1024 * 1024}
            assert_match {*backlog_tier_offset=*} [$primary info replication]
            assert_equal [expr {$activations + 1}] [tier_info $primary activations]
            assert_equal [expr {$tiered + 1}] [tier_info $primary tiered_replicas]

            # No gap between the tier and the in-memory backlog.
            set backlog_start [getInfoProperty [$primary info replication] repl_backlog_first_byte_offset]
            set tier_end [expr {[tier_info $primary first_byte_offset] + [tier_info $primary size]}]
            assert {$tier_end >= $backlog_start}

            resume_process $replica_pid

            # Once the replica drained the tier it moves back to memory.
            wait_for_condition 200 100 {
                [tier_info $primary readers] == 0
            } else {
                fail "replica did not catch up from the disk tier"
            }
            assert_in_sync $primary $replica
            assert {[tier_info $primary sent_bytes] > 10 * 1024 * 1024}
            # The replica was never dropped and resynced.
            assert_equal $full_syncs [sync_stat $primary sync_full]
            verify_no_log_message 0 "*overcoming of output buffer limits*" 0
            # Nothing references the tier anymore.
            wait_for_condition 50 100 {
                [tier_info $primary active] == 0
            } else {
                fail "tier was not released after the replica caught up"
            }
        }

        test {Replica that drops while reading from disk partially resyncs from the tier} {
            setup_tiered_replication $primary $replica $primary_host $primary_port
            set full_syncs [sync_stat $primary sync_full]
            set partial_ok [sync_stat $primary sync_partial_ok]
            set psyncs [tier_info $primary psyncs]

            # Let the replica consume part of the tier, so that whatever it
            # loses in socket buffers when the link drops is in the tier. It
            # may drain the whole tier before we stop it: try again then.
            for {set attempt 0} {$attempt < 5} {incr attempt} {
                pause_process $replica_pid
                write_chunks $primary 30 key:$attempt 1
                wait_tiered $primary $replica_pid
                set start [tier_info $primary first_byte_offset]
                set size [tier_info $primary size]

                resume_process $replica_pid
                wait_for_condition 1000 1 {
                    [replica_ack_offset $primary] > $start + $size / 4
                } else {
                    fail "replica did not read from the tier"
                }
                pause_process $replica_pid
                if {[tier_info $primary readers] == 1} break
            }
            if {[tier_info $primary readers] != 1} {
                resume_process $replica_pid
                fail "replica caught up before the link could be dropped"
            }

            # Drop the link while the replica is still reading from disk. The
            # tier keeps what it needs (repl-backlog-tiering-retention).
            $primary client kill type replica
            wait_for_condition 50 100 {
                [tier_info $primary readers] == 0
            } else {
                resume_process $replica_pid
                fail "replica link was not dropped"
            }
            assert_equal 1 [tier_info $primary active]

            resume_process $replica_pid
            assert_in_sync $primary $replica

            assert_equal [expr {$psyncs + 1}] [tier_info $primary psyncs]
            assert_equal [expr {$partial_ok + 1}] [sync_stat $primary sync_partial_ok]
            assert_equal $full_syncs [sync_stat $primary sync_full]
        }

        test {Replica disconnected while in memory partially resyncs after more than the backlog was written} {
            setup_tiered_replication $primary $replica $primary_host $primary_port
            set full_syncs [sync_stat $primary sync_full]
            set partial_ok [sync_stat $primary sync_partial_ok]
            set psyncs [tier_info $primary psyncs]
            set activations [tier_info $primary activations]

            # The replica is caught up and acknowledged everything.
            $primary set before 1
            wait_for_ofs_sync $primary $replica
            pause_process $replica_pid
            $primary client kill type replica
            wait_for_condition 50 100 {
                [tier_info $primary psync_holds] == 1
            } else {
                resume_process $replica_pid
                fail "disconnected replica left no hold"
            }
            assert_equal 0 [tier_info $primary active]

            # 20x the in-memory backlog while it is away: the hold starts the
            # tier before the backlog drops data the replica needs.
            write_chunks $primary 20
            assert_equal 1 [tier_info $primary active]
            assert_equal [expr {$activations + 1}] [tier_info $primary activations]
            verify_log_message 0 "*disconnected replica may still need offset*" 0

            resume_process $replica_pid
            assert_in_sync $primary $replica
            assert_equal [expr {$psyncs + 1}] [tier_info $primary psyncs]
            assert_equal [expr {$partial_ok + 1}] [sync_stat $primary sync_partial_ok]
            assert_equal $full_syncs [sync_stat $primary sync_full]

            # The PSYNC consumed the hold; once caught up nothing needs the tier.
            assert_equal 0 [tier_info $primary psync_holds]
            wait_for_condition 50 100 {
                [tier_info $primary active] == 0
            } else {
                fail "tier was not released after the replica caught up"
            }
        }

        test {FLUSHALL keeps the disk tier, the replica continues its stream} {
            setup_tiered_replication $primary $replica $primary_host $primary_port
            set full_syncs [sync_stat $primary sync_full]
            set resets [tier_info $primary resets]

            pause_process $replica_pid
            write_chunks $primary 20
            wait_tiered $primary $replica_pid

            # FLUSHALL is just another command in the replication stream.
            $primary flushall
            assert_equal 1 [tier_info $primary active]
            assert_equal 1 [tier_info $primary readers]
            write_chunks $primary 2 after

            resume_process $replica_pid
            assert_in_sync $primary $replica
            assert_equal 2000 [$replica dbsize]
            assert_equal $resets [tier_info $primary resets]
            assert_equal $full_syncs [sync_stat $primary sync_full]
        }

        test {Replication ID change drops the tier and its readers} {
            setup_tiered_replication $primary $replica $primary_host $primary_port
            set full_syncs [sync_stat $primary sync_full]
            set resets [tier_info $primary resets]

            pause_process $replica_pid
            write_chunks $primary 20
            wait_tiered $primary $replica_pid

            # The stream on disk no longer belongs to the current history.
            $primary debug change-repl-id
            wait_for_condition 50 100 {
                [tier_info $primary active] == 0
            } else {
                resume_process $replica_pid
                fail "tier was not dropped after the replication ID changed"
            }
            assert_equal 0 [tier_info $primary readers]
            assert_equal [expr {$resets + 1}] [tier_info $primary resets]
            verify_log_message 0 "*dropping tier*replication ID changed*" 0

            resume_process $replica_pid
            wait_for_condition 100 100 {
                [sync_stat $primary sync_full] > $full_syncs
            } else {
                fail "replica did not resync after the tier was dropped"
            }
            assert_in_sync $primary $replica
        }

        test {Tier start follows the reader and the tier is released once it caught up} {
            setup_tiered_replication $primary $replica $primary_host $primary_port

            pause_process $replica_pid
            write_chunks $primary 20
            wait_tiered $primary $replica_pid
            set start [tier_info $primary first_byte_offset]
            set size [tier_info $primary size]

            # Let the replica read and acknowledge part of the tier (the tier
            # start follows acknowledged data, even once the replica caught up
            # and is served from memory again), then stop it again.
            resume_process $replica_pid
            wait_for_condition 500 10 {
                [replica_ack_offset $primary] > $start + $size / 4
            } else {
                fail "replica did not read from the tier"
            }
            pause_process $replica_pid
            # Nothing references the data the replica already read anymore.
            wait_for_condition 50 100 {
                [tier_info $primary active] == 0 || [tier_info $primary first_byte_offset] > $start
            } else {
                resume_process $replica_pid
                fail "tier start did not follow the reader (tier started at $start)"
            }
            resume_process $replica_pid

            # No reader, no PSYNC hold, nobody behind: released right away
            # rather than after repl-backlog-tiering-retention.
            wait_for_condition 50 100 {
                [tier_info $primary active] == 0
            } else {
                fail "unreferenced tier was not released"
            }
            verify_log_message 0 "*releasing tier*no replica needs it*" 0
            assert_in_sync $primary $replica
        }

        test {Disconnected reader's data is only kept for the retention period} {
            setup_tiered_replication $primary $replica $primary_host $primary_port
            $primary config set repl-backlog-tiering-retention 1
            set full_syncs [sync_stat $primary sync_full]

            pause_process $replica_pid
            write_chunks $primary 20
            wait_tiered $primary $replica_pid
            $primary client kill type replica
            # Once the hold expires nothing references the tier.
            wait_for_condition 50 100 {
                [tier_info $primary active] == 0
            } else {
                resume_process $replica_pid
                fail "tier was not released after the retention period"
            }
            resume_process $replica_pid

            wait_for_condition 100 100 {
                [sync_stat $primary sync_full] > $full_syncs
            } else {
                fail "replica did not resync after the tier was released"
            }
            assert_in_sync $primary $replica
        }

        test {repl-backlog-tiering-max-size disconnects readers that fall too far behind} {
            setup_tiered_replication $primary $replica $primary_host $primary_port
            $primary config set repl-backlog-tiering-max-size 4mb
            set evicted [tier_info $primary evicted_readers]
            set full_syncs [sync_stat $primary sync_full]

            pause_process $replica_pid
            write_chunks $primary 20
            wait_for_condition 100 100 {
                [tier_info $primary evicted_readers] > $evicted
            } else {
                resume_process $replica_pid
                fail "reader was not evicted by repl-backlog-tiering-max-size"
            }
            assert {[tier_info $primary size] <= 8 * 1024 * 1024}
            # An evicted reader can't PSYNC from the tier, so nothing holds it.
            wait_for_condition 50 100 {
                [tier_info $primary active] == 0
            } else {
                resume_process $replica_pid
                fail "tier was not released after its only reader was evicted"
            }
            resume_process $replica_pid
            wait_for_condition 100 100 {
                [sync_stat $primary sync_full] > $full_syncs
            } else {
                fail "replica did not resync after being evicted"
            }
            assert_in_sync $primary $replica
        }

        test {Replica is disconnected as before when tiering is disabled} {
            setup_tiered_replication $primary $replica $primary_host $primary_port
            $primary config set repl-backlog-tiering-enabled no
            # A tier left over from earlier is released by the next cron run.
            wait_for_condition 50 100 {
                [tier_info $primary active] == 0
            } else {
                fail "tier was not released after disabling tiering"
            }
            set full_syncs [sync_stat $primary sync_full]

            pause_process $replica_pid
            write_chunks $primary 20
            wait_for_log_messages 0 {"*overcoming of output buffer limits*"} 0 100 100
            set active [tier_info $primary active]
            resume_process $replica_pid
            assert_equal 0 $active

            wait_for_condition 100 100 {
                [sync_stat $primary sync_full] > $full_syncs
            } else {
                fail "replica did not resync after being disconnected"
            }
            assert_in_sync $primary $replica
        }

        # Leave the replica detached for any following test.
        catch {$replica replicaof no one}
    }
}
