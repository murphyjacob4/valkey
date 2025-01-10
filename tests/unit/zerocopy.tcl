proc fill_until_zerocopy_in_flight_greater_than {primary count populate_count populate_size} {
    set i 0
    while 1 {
        if {[expr $i * $populate_count * $populate_size] > [expr 10 * 1024 * 1024 * 1024]} {
            # We wrote 10 GiB of data. Give up now.
            fail "After 10 GiB of data, still don't have $count in flight zero copy writes"
        }
        incr i
        if {[status $primary zero_copy_writes_in_flight] <= $count} {
            populate $populate_count "zerocopy_key:$i:" $populate_size 0
        } else {
            break
        }
    }
}

proc fill_until_zerocopy_acks_stop {primary} {
    # Fill using batches of ~1MiB
    fill_until_zerocopy_in_flight_greater_than $primary 0 103 10240
}

start_server {tags {"repl zerocopy external:skip"}} {
start_server {} {
    set primary [srv 0 client]
    set primary_host [srv 0 host]
    set primary_port [srv 0 port]

    set replica_pid [s -1 process_id]
    set replica [srv -1 client]
    set replica_host [srv -1 host]
    set replica_port [srv -1 port]

    $primary debug zerocopy-for-loopback 1
    $primary config set repl-timeout 1200 ;# 20 minutes (for valgrind and slow machines)
    $replica config set repl-timeout 1200 ;# 20 minutes (for valgrind and slow machines)
    $primary config set client-output-buffer-limit "replica 0 0 0"
    $replica replicaof $primary_host $primary_port
    wait_for_sync $replica

    test {Small writes do not go through zerocopy} {
        set initial_zerocopy_writes [s 0 zero_copy_writes_processed]
        set initial_zerocopy_mem [s 0 used_memory_zero_copy_tracking]

        populate 1 "small_key:" 1024 0
        wait_for_sync $replica

        assert_equal [s 0 zero_copy_writes_processed] $initial_zerocopy_writes
        assert_equal [s 0 used_memory_zero_copy_tracking] $initial_zerocopy_mem
        assert_equal [s 0 zero_copy_writes_in_flight] 0
    }

    test {Large writes go through zerocopy} {
        set initial_zerocopy_writes [s 0 zero_copy_writes_processed]
        set initial_zerocopy_mem [s 0 used_memory_zero_copy_tracking]

        populate 1 "big_key:" 10240 0
        wait_for_sync $replica

        assert_equal [s 0 zero_copy_writes_processed] [expr {$initial_zerocopy_writes + 1}]
        assert {[s 0 used_memory_zero_copy_tracking] > $initial_zerocopy_mem}
        assert_equal [s 0 zero_copy_writes_in_flight] 0
    }

    test {Zero copy writes trim backlog once received} {
        # Set backlog to 64 KiB
        $primary config set repl-backlog-size [expr 64*1024]
        assert {[s 0 repl_backlog_histlen] < [expr 64 * 1024 + 16*1024]}

        populate 100 "big_key:" 10240 0
        wait_for_ofs_sync $primary $replica

        # In-flight zero copy writes should get their ACKs
        wait_for_condition 100 100 {
            [s 0 zero_copy_writes_in_flight] == 0
        } else {
            fail "In flight zero copy writes never completed"
        }

        # Backlog should be trimmed to repl-backlog-size (plus up to PROTO_REPLY_CHUNK_BYTES/16KiB)
        wait_for_condition 100 100 {
            [s 0 repl_backlog_histlen] < [expr 64*1024 + 16*1024]
        } else {
            fail "Backlog should eventually be trimmed back to repl-backlog-size"
        }
    }

    test {Zero copy handles late ACKs gracefully} {
        # Pause the replica process
        pause_process $replica_pid

        # Keep filling until we see the in flight zero copy writes is greater than 0
        fill_until_zerocopy_acks_stop $primary

        # Add an additional 1 MiB, which should grow the repl backlog beyond the max
        populate 1 "zerocopy_key:extra:" [expr 1024 * 1024] 0

        assert {[s 0 repl_backlog_histlen] > [expr 64*1024 + 16*1024]}

        # Resume the replica process
        resume_process $replica_pid
        wait_for_ofs_sync $primary $replica

        # In-flight zero copy writes should get their ACKs
        wait_for_condition 100 100 {
            [s 0 zero_copy_writes_in_flight] == 0
        } else {
            fail "In flight zero copy writes never completed"
        }

        # Backlog should be trimmed to repl-backlog-size (plus up to PROTO_REPLY_CHUNK_BYTES/16KiB)
        wait_for_condition 100 100 {
            [s 0 repl_backlog_histlen] < [expr 64*1024 + 16*1024]
        } else {
            fail "Backlog should eventually be trimmed back to repl-backlog-size"
        }
    }

    test {In-flight zerocopy writes are gracefully flushed when responsive replica is killed} {
        # Accumulate some in flight writes
        pause_process $replica_pid
        fill_until_zerocopy_acks_stop $primary

        # Add an additional 1 MiB, which should grow the repl backlog beyond the max
        populate 1 "zerocopy_key:extra:" [expr 1024 * 1024] 0
        assert {[s 0 repl_backlog_histlen] > [expr 64*1024 + 16*1024]}

        # Kill the replica client
        assert {[$primary client kill type replica] > 0}

        # Should now be draining
        assert_equal [s 0 draining_clients] 1

        # Resume the replica, and the draining should end gracefully
        resume_process $replica_pid
        wait_for_condition 100 100 {
            [s 0 draining_clients] eq 0
        } else {
            fail "Client never finished draining"
        }
        assert_equal [s 0 zero_copy_clients_force_closed] 0

        # Backlog should be trimmed to repl-backlog-size (plus up to PROTO_REPLY_CHUNK_BYTES/16KiB)
        wait_for_condition 100 100 {
            [s 0 repl_backlog_histlen] < [expr 64*1024 + 16*1024]
        } else {
            fail "Backlog should eventually be trimmed back to repl-backlog-size"
        }

        # Replica should be able to resync
        wait_for_ofs_sync $primary $replica
    }

    test {In-flight zerocopy writes are forcefully closed when unresponsive replica is killed} {
        # Accumulate some in flight writes
        pause_process $replica_pid
        fill_until_zerocopy_acks_stop $primary

        # Add an additional 1 MiB, which should grow the repl backlog beyond the max
        populate 1 "zerocopy_key:extra:" [expr 1024 * 1024] 0
        assert {[s 0 repl_backlog_histlen] > [expr 64*1024 + 16*1024]}

        # Kill the replica client
        assert {[$primary client kill type replica] > 0}

        # Should now be draining
        assert_equal [s 0 draining_clients] 1

        # Keep the replica paused, the primary should force close it after some time
        wait_for_condition 100 100 {
            [s 0 draining_clients] eq 0
        } else {
            fail "Client never finished draining"
        }
        assert_equal [s 0 zero_copy_clients_force_closed] 1

        # Backlog should be trimmed to repl-backlog-size (plus up to PROTO_REPLY_CHUNK_BYTES/16KiB)
        wait_for_condition 100 100 {
            [s 0 repl_backlog_histlen] < [expr 64*1024 + 16*1024]
        } else {
            fail "Backlog should eventually be trimmed back to repl-backlog-size"
        }

        resume_process $replica_pid

        # Replica should be able to resync
        wait_for_ofs_sync $primary $replica
    }

    test {Zero copy tracker grows and shrinks as needed} {
        # Force enable zerocopy for all writes to force many tracking entries.
        $primary config set tcp-zerocopy-min-write-size 0

        # Add an initial key to ensure our zero copy tracker is instantiated
        populate 1 "zerocopy_key:extra:" 1024 0
        set initial_zerocopy_mem [s 0 used_memory_zero_copy_tracking]

        # Accumulate a lot of in flight writes
        pause_process $replica_pid
        fill_until_zerocopy_acks_stop $primary
        fill_until_zerocopy_in_flight_greater_than $primary 1024 1 1
        assert {[s 0 used_memory_zero_copy_tracking] > $initial_zerocopy_mem}

        # Flush the writes
        resume_process $replica_pid
        wait_for_condition 100 100 {
            [s 0 zero_copy_writes_in_flight] == 0
        } else {
            fail "In flight zero copy writes never completed"
        }

        # Buffer should shrink back to original size
        assert_equal [s 0 used_memory_zero_copy_tracking] $initial_zerocopy_mem
    }
}
}