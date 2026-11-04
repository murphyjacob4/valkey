set testmodule [file normalize tests/modules/test_lazyfree.so]

tags {"modules repl network external:skip"} {

start_server {overrides {
    save ""
    forkless-infrastructure-enabled yes
    forkless-policy prefer-forkless
    repl-diskless-sync yes
    repl-diskless-sync-delay 0
}} {
    set primary [srv 0 client]
    set primary_host [srv 0 host]
    set primary_port [srv 0 port]
    $primary set k v

    start_server {overrides {save "" repl-diskless-load swapdb}} {
        set replica [srv 0 client]

        test {Replica logs swapdb reason when skipping inband-repl capability} {
            set loglines [count_log_lines 0]
            set before_fallbacks [s -1 forkless_fallbacks_missing_inband_repl]

            $replica replicaof $primary_host $primary_port
            wait_for_sync $replica

            assert_equal [expr {$before_fallbacks + 1}] [s -1 forkless_fallbacks_missing_inband_repl]
            verify_log_message 0 "*Skipping inband-repl capability for forkless sync*swapdb*" $loglines
        }
    }

    start_server {overrides {save "" repl-diskless-load disabled}} {
        set replica [srv 0 client]
        $replica module load $testmodule

        test {Replica logs module name when skipping inband-repl capability} {
            set loglines [count_log_lines 0]
            set before_fallbacks [s -1 forkless_fallbacks_missing_inband_repl]

            $replica replicaof $primary_host $primary_port
            wait_for_sync $replica

            assert_equal [expr {$before_fallbacks + 1}] [s -1 forkless_fallbacks_missing_inband_repl]
            verify_log_message 0 "*Skipping inband-repl capability for forkless sync*module 'lazyfreetest'*VALKEYMODULE_OPTIONS_HANDLE_FORKLESS*" $loglines
        }
    }

    start_server {overrides {save "" repl-diskless-load disabled}} {
        set replica [srv 0 client]
        $replica module load $testmodule forkless

        test {Replica advertises inband-repl when modules opt into forkless} {
            set loglines [count_log_lines 0]
            set before_fallbacks [s -1 forkless_fallbacks_missing_inband_repl]

            $replica replicaof $primary_host $primary_port
            wait_for_sync $replica

            assert_equal $before_fallbacks [s -1 forkless_fallbacks_missing_inband_repl]
            verify_no_log_message 0 "*Skipping inband-repl capability for forkless sync*" $loglines
        }
    }
}

}
