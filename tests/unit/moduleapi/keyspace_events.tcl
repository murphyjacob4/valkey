set testmodule [file normalize tests/modules/keyspace_events.so]

tags "modules" {
    start_server [list overrides [list loadmodule "$testmodule"]] {

        test {Test loaded key space event} {
            r set x 1
            r hset y f v
            r lpush z 1 2 3
            r sadd p 1 2 3
            r zadd t 1 f1 2 f2
            r xadd s * f v
            r debug reload
            assert_equal {1 x} [r keyspace.is_key_loaded x]
            assert_equal {1 y} [r keyspace.is_key_loaded y]
            assert_equal {1 z} [r keyspace.is_key_loaded z]
            assert_equal {1 p} [r keyspace.is_key_loaded p]
            assert_equal {1 t} [r keyspace.is_key_loaded t]
            assert_equal {1 s} [r keyspace.is_key_loaded s]
        }

        test {Nested multi due to RM_Call} {
            r del multi
            r del lua

            r set x 1
            r set x_copy 1
            r keyspace.del_key_copy x
            r keyspace.incr_case1 x
            r keyspace.incr_case2 x
            r keyspace.incr_case3 x
            assert_equal {} [r get multi]
            assert_equal {} [r get lua]
            r get x
        } {3}
        
        test {Nested multi due to RM_Call, with client MULTI} {
            r del multi
            r del lua

            r set x 1
            r set x_copy 1
            r multi
            r keyspace.del_key_copy x
            r keyspace.incr_case1 x
            r keyspace.incr_case2 x
            r keyspace.incr_case3 x
            r exec
            assert_equal {1} [r get multi]
            assert_equal {} [r get lua]
            r get x
        } {3}
        
        test {Nested multi due to RM_Call, with EVAL} {
            r del multi
            r del lua

            r set x 1
            r set x_copy 1
            r eval {
                redis.pcall('keyspace.del_key_copy', KEYS[1])
                redis.pcall('keyspace.incr_case1', KEYS[1])
                redis.pcall('keyspace.incr_case2', KEYS[1])
                redis.pcall('keyspace.incr_case3', KEYS[1])
            } 1 x
            assert_equal {} [r get multi]
            assert_equal {1} [r get lua]
            r get x
        } {3}

        test {Test module key space event} {
            r keyspace.notify x
            assert_equal {1 x} [r keyspace.is_module_key_notified x]
        }

        test "Keyspace notifications: module events test" {
            r config set notify-keyspace-events Kd
            r del x
            set rd1 [valkey_deferring_client]
            assert_equal {1} [psubscribe $rd1 *]
            r keyspace.notify x
            assert_equal {pmessage * __keyspace@9__:x notify} [$rd1 read]
            $rd1 close
        }

        test "Keyspace notifications: low-level VM_DeleteKey and VM_UnlinkKey" {
            r config set notify-keyspace-events KEA
            r set mykey "hello"
            set rd1 [valkey_deferring_client]
            assert_equal {1} [psubscribe $rd1 *]

            # VM_DeleteKey should emit del notification
            assert_equal {OK} [r keyspace.del_key mykey]
            assert_equal {pmessage * __keyspace@9__:mykey del} [$rd1 read]
            assert_equal {pmessage * __keyevent@9__:del mykey} [$rd1 read]

            # VM_UnlinkKey should emit del notification
            r set mykey2 "world"
            assert_equal {pmessage * __keyspace@9__:mykey2 set} [$rd1 read]
            assert_equal {pmessage * __keyevent@9__:set mykey2} [$rd1 read]

            assert_equal {OK} [r keyspace.unlink_key mykey2]
            assert_equal {pmessage * __keyspace@9__:mykey2 del} [$rd1 read]
            assert_equal {pmessage * __keyevent@9__:del mykey2} [$rd1 read]

            $rd1 close
        }

        test "Keyspace notifications: low-level VM_StringSet does not emit del on overwrite" {
            r config set notify-keyspace-events KEA
            r set mykey "hello"
            set rd1 [valkey_deferring_client]
            assert_equal {1} [psubscribe $rd1 *]

            # Overwriting via VM_StringSet should emit 'set', not 'del'
            assert_equal {OK} [r keyspace.string_set mykey "updated"]
            assert_equal {pmessage * __keyspace@9__:mykey set} [$rd1 read]
            assert_equal {pmessage * __keyevent@9__:set mykey} [$rd1 read]

            $rd1 close
        }

        test "Keyspace notifications: VALKEYMODULE_OPEN_KEY_NO_KEYSPACE_EVENTS suppresses events" {
            r config set notify-keyspace-events KEA
            r set mykey "hello"
            set rd1 [valkey_deferring_client]
            assert_equal {1} [psubscribe $rd1 *]

            # Deleting with NO_KEYSPACE_EVENTS should not emit any keyspace events
            assert_equal {OK} [r keyspace.del_key_nonotify mykey]

            # Trigger a known event to ensure channel is flushed and verify no del was sent
            r set probe "value"
            assert_equal {pmessage * __keyspace@9__:probe set} [$rd1 read]
            assert_equal {pmessage * __keyevent@9__:set probe} [$rd1 read]

            $rd1 close
        }

        test "Keyspace notifications: VALKEYMODULE_OPTION_NO_IMPLICIT_KEYSPACE_EVENTS suppresses events" {
            r config set notify-keyspace-events KEA
            assert_equal {OK} [r keyspace.set_no_implicit_keyspace_events]

            r set mykey "hello"
            set rd1 [valkey_deferring_client]
            assert_equal {1} [psubscribe $rd1 *]

            assert_equal {OK} [r keyspace.del_key mykey]

            # Trigger a known event to ensure channel is flushed and verify no del was sent
            r set probe "value"
            assert_equal {pmessage * __keyspace@9__:probe set} [$rd1 read]
            assert_equal {pmessage * __keyevent@9__:set probe} [$rd1 read]

            $rd1 close
            assert_equal {OK} [r keyspace.clear_no_implicit_keyspace_events]
        }

        test "Keyspace notifications: low-level VM_SetExpire emits expire and persist" {
            r config set notify-keyspace-events KEA
            r set mykey "hello"
            set rd1 [valkey_deferring_client]
            assert_equal {1} [psubscribe $rd1 *]

            assert_equal {OK} [r keyspace.set_expire mykey 100000]
            assert_equal {pmessage * __keyspace@9__:mykey expire} [$rd1 read]
            assert_equal {pmessage * __keyevent@9__:expire mykey} [$rd1 read]

            assert_equal {OK} [r keyspace.set_expire mykey -1]
            assert_equal {pmessage * __keyspace@9__:mykey persist} [$rd1 read]
            assert_equal {pmessage * __keyevent@9__:persist mykey} [$rd1 read]

            $rd1 close
        }

        test {Test expired key space event} {
            set prev_expired [s expired_keys]
            r set exp 1 PX 10
            wait_for_condition 100 10 {
                [s expired_keys] eq $prev_expired + 1
            } else {
                fail "key not expired"
            }
            assert_equal [r get testkeyspace:expired] 1
        }

        test {MOVE restores client DB after module keyspace notification} {
            # MOVE fires move_from/move_to notifications on the source and
            # destination DBs. The module subscribes to NOTIFY_GENERIC, and
            # the bug left the client selected on the destination DB.
            r flushall
            r select 0
            r set movekey value

            # The client must stay on its original DB (c->db unchanged).
            assert_equal 1 [r move movekey 10]
            assert_match {*db=0*} [r client info]

            # If the client was still on db10, this would fail with
            # "source and destination objects are the same" instead of 0.
            assert_equal 0 [r move movekey 10]
            assert_match {*db=0*} [r client info]
        } {} {singledb:skip}

        test {COPY restores client DB after module keyspace notification} {
            # COPY fires a copy_to notification on the destination DB. The
            # module subscribes to NOTIFY_GENERIC, and the bug left the client
            # selected on the destination DB.
            r flushall
            r select 0
            r set copykey value

            # The client must stay on its original DB (c->db unchanged).
            assert_equal 1 [r copy copykey copykey DB 10]
            assert_match {*db=0*} [r client info]

            # If the client was still on db10, this would fail with
            # "source and destination objects are the same" instead of 0
            assert_equal 0 [r copy copykey copykey DB 10]
            assert_match {*db=0*} [r client info]
        } {} {singledb:skip}

        test "Unload the module - testkeyspace" {
            assert_equal {OK} [r module unload testkeyspace]
        }

        test "Verify RM_StringDMA with expiration are not causing invalid memory access" {
            assert_equal {OK} [r set x 1 EX 1]
        }
    }

    start_server {} {
        test {OnLoad failure will handle un-registration} {
            catch {r module load $testmodule noload}
            r set x 1
            r hset y f v
            r lpush z 1 2 3
            r sadd p 1 2 3
            r zadd t 1 f1 2 f2
            r xadd s * f v
            r ping
        }
    }
}
