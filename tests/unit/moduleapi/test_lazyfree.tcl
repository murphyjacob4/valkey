set testmodule [file normalize tests/modules/test_lazyfree.so]

start_server {tags {"modules"}} {
    r module load $testmodule

    test "modules allocated memory can be reclaimed in the background" {
        set orig_mem [s used_memory]
        set rd [valkey_deferring_client]

        # LAZYFREE_THRESHOLD is 64
        $rd client reply off
        for {set i 0} {$i < 10000} {incr i} {
            $rd lazyfreelink.insert lazykey $i
            if {$i % 1000 == 0} {$rd flush}
        }
        $rd client reply on
        assert_equal OK [$rd read]

        assert {[r lazyfreelink.len lazykey] == 10000}

        set peak_mem [s used_memory]
        assert {[r unlink lazykey] == 1}
        assert {$peak_mem > $orig_mem+10000}
        wait_for_condition 50 100 {
            [s used_memory] < $peak_mem &&
            [s used_memory] < $orig_mem*2 &&
            [string match {*lazyfreed_objects:1*} [r info Memory]]
        } else {
            fail "Module memory is not reclaimed by UNLINK"
        }
    }
}

start_server {tags {"modules"} overrides {forkless-infrastructure-enabled yes forkless-policy prefer-forkless save ""}} {
    r module load $testmodule forkless

    test "FLUSHALL cancels a forkless bgsave that is still closing its file" {
        # Block the lazyfree BIO worker, so the close-and-rename job a
        # finished forkless save queues behind it cannot run yet.
        for {set i 0} {$i < 100} {incr i} {
            r lazyfreelink.insert lazykey $i
        }
        r lazyfreelink.holdfree 1
        r unlink lazykey

        r set stale v
        set loglines [count_log_lines 0]
        r bgsave
        wait_for_log_messages 0 {"*created background thread to perform snapshot file close and rename*"} $loglines 100 10

        r config set save "3600 1"
        r flushall
        r lazyfreelink.holdfree 0
        wait_for_condition 50 100 {
            [s rdb_bgsave_in_progress] == 0
        } else {
            fail "forkless bgsave did not finish"
        }

        # dump.rdb must still hold FLUSHALL's empty snapshot.
        r debug reload nosave
        assert_equal [r dbsize] 0
    } {} {needs:debug}
}

start_server {tags {"modules network external:skip"} overrides {save ""}} {
    set primary [srv 0 client]
    set primary_host [srv 0 host]
    set primary_port [srv 0 port]
    $primary set synced_key primary_val

    start_server {overrides {
        forkless-infrastructure-enabled yes
        forkless-policy prefer-forkless
        repl-diskless-load disabled
        save "3600 1"
    }} {
        set replica [srv 0 client]
        $replica module load $testmodule forkless

        test "Full sync with disk load cancels a forkless bgsave closing its file" {
            for {set i 0} {$i < 100} {incr i} {
                $replica lazyfreelink.insert lazykey $i
            }
            $replica lazyfreelink.holdfree 1
            $replica unlink lazykey

            $replica set stale_key replica_val
            set loglines [count_log_lines 0]
            $replica bgsave
            wait_for_log_messages 0 {"*created background thread to perform snapshot file close and rename*"} $loglines 100 10

            $replica replicaof $primary_host $primary_port
            wait_for_sync $replica
            assert_equal "primary_val" [$replica get synced_key]
            assert_equal "" [$replica get stale_key]

            $replica lazyfreelink.holdfree 0
            wait_for_condition 50 100 {
                [s 0 rdb_bgsave_in_progress] == 0
            } else {
                fail "forkless bgsave did not finish"
            }

            # dump.rdb must still hold the synced RDB from the primary rather
            # than the pre-sync snapshot from the replica's forkless save.
            $replica replicaof no one
            $replica debug reload nosave
            assert_equal "primary_val" [$replica get synced_key]
            assert_equal "" [$replica get stale_key]
        } {} {needs:debug}
    }

    start_server {overrides {
        forkless-infrastructure-enabled yes
        forkless-policy prefer-forkless
        repl-diskless-load swapdb
        save ""
    }} {
        set replica [srv 0 client]
        $replica module load $testmodule forkless swapdb

        test "Full sync with swapdb cancels a forkless bgsave closing its file" {
            $replica set baseline_key clean_val
            $replica save

            for {set i 0} {$i < 100} {incr i} {
                $replica lazyfreelink.insert lazykey $i
            }
            $replica lazyfreelink.holdfree 1
            $replica unlink lazykey

            $replica set stale_key replica_val
            set loglines [count_log_lines 0]
            $replica bgsave
            wait_for_log_messages 0 {"*created background thread to perform snapshot file close and rename*"} $loglines 100 10

            set sync_loglines [count_log_lines 0]
            $replica replicaof $primary_host $primary_port
            wait_for_sync $replica
            wait_for_log_messages 0 {"*Swapping active DB with loaded DB*"} $sync_loglines 50 20
            assert_equal "primary_val" [$replica get synced_key]

            $replica lazyfreelink.holdfree 0
            wait_for_condition 50 100 {
                [s 0 rdb_bgsave_in_progress] == 0
            } else {
                fail "forkless bgsave did not finish"
            }

            # dump.rdb must not be overwritten with the discarded pre-sync DB.
            $replica replicaof no one
            $replica debug reload nosave
            assert_equal "clean_val" [$replica get baseline_key]
            assert_equal "" [$replica get stale_key]
        } {} {needs:debug}
    }
}
