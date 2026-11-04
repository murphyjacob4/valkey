proc get_function_code {args} {
    return [format "#!%s name=%s\nserver.register_function('%s', function(KEYS, ARGV)\n %s \nend)" [lindex $args 0] [lindex $args 1] [lindex $args 2] [lindex $args 3]]
}

tags {"check-rdb external:skip logreqres:skip"} {
    # Legacy snapshot: "emptied" has no paths; "kept" contains p -> f = v.
    test {RDB loading skips a legacy empty Path Hash} {
        set server_path [tmpdir "server.rdb-path-hash-empty-key"]
        exec cp tests/assets/path-hash-empty-key.rdb $server_path
        start_server [list overrides [list dir $server_path dbfilename path-hash-empty-key.rdb]] {
            r select 0
            assert_equal 1 [r dbsize]
            assert_equal 0 [r exists emptied]
            assert_equal {v} [r phget kept p f]
            verify_log_message 0 "*skipping empty key: emptied*" 0
        }
    }

    foreach fixture {path-hash-empty-key.rdb corrupt_empty_keys.rdb} {
        test "Check legacy empty containers: $fixture" {
            set result [exec $::VALKEY_CHECK_RDB_BIN tests/assets/$fixture]
            assert_match {*RDB looks OK!*} $result
            set result [exec $::VALKEY_CHECK_RDB_BIN tests/assets/$fixture --stats --format info]
            assert_match {*RDB looks OK!*} $result
        }
    }

    test {Check old valid RDB} {
        catch {
            exec $::VALKEY_CHECK_RDB_BIN tests/assets/encodings.rdb
        } result
        assert_match {*\[offset ???\] \\o/ RDB looks OK! \\o/*} $result
    }

    test {Check --output without a file name prints usage} {
        catch {
            exec $::VALKEY_CHECK_RDB_BIN tests/assets/encodings.rdb --output
        } result
        assert_match {Usage: *} $result
    }

    test {Check foreign RDB without unknown data} {
        catch {
            exec $::VALKEY_CHECK_RDB_BIN tests/assets/encodings-rdb12.rdb
        } result
        assert_match {*\[offset ?\] Foreign RDB version 12 detected*} $result
        assert_match {*\[offset ???\] \\o/ RDB looks OK, but loading requires config 'rdb-version-check relaxed'*} $result
    }

    test {Check foreign RDB with unknown data} {
        catch {
            exec $::VALKEY_CHECK_RDB_BIN tests/assets/encodings-rdb75-unknown-types.rdb
        } result
        assert_match {*\[offset ?\] Foreign RDB version 75 detected*} $result
        assert_match {*--- RDB ERROR DETECTED ---*} $result
        assert_match {*\[offset ??\] Unknown object type 150 in RDB file with foreign version 75*} $result
        assert_no_match {*RDB looks OK*} $result
    }

    test {Check future RDB without unknown data} {
        catch {
            exec $::VALKEY_CHECK_RDB_BIN tests/assets/encodings-rdb987.rdb
        } result
        assert_match {*\[offset ?\] Future RDB version 987 detected*} $result
        assert_match {*\[offset ???\] \\o/ RDB looks OK, but loading requires config 'rdb-version-check relaxed'*} $result
    }

    test {Check future RDB with unknown data} {
        catch {
            exec $::VALKEY_CHECK_RDB_BIN tests/assets/encodings-rdb987-unknown-types.rdb
        } result
        assert_match {*\[offset ?\] Future RDB version 987 detected*} $result
        assert_match {*--- RDB ERROR DETECTED ---*} $result
        assert_match {*\[offset ??\] Unknown object type 150 in RDB file with future version 987*} $result
        assert_no_match {*RDB looks OK*} $result
    }

    test {Check RDB stats when the highest selected DB has no keys} {
        # SELECTDB 2, EOF, zero checksum.
        set rdb [tmpfile empty-last-db.rdb]
        write_binary_file $rdb [binary format a9H* REDIS0009 fe02ff0000000000000000]
        catch {
            exec $::VALKEY_CHECK_RDB_BIN $rdb --stats --format info
        } result
        assert_match {*db.2.type.string.keys.total:0*} $result
    }
}

tags {"check-rdb network external:skip logreqres:skip"} {
    start_server {} {
        foreach mode {lz4 zstd} {
            test "valkey-check-rdb validates the contents of a [string toupper $mode]-compressed RDB" {
                if {$mode eq "zstd" && ![config_value_supported r rdbcompression zstd]} {
                    skip "zstd is not supported by this build"
                }

                r config set rdbcompression $mode
                with_cleanup {
                    r flushall
                    r set "$mode:key" [string repeat "payload " 200]
                    r save

                    set dump_rdb [file join [lindex [r config get dir] 1] dump.rdb]
                    set failed [catch {
                        exec $::VALKEY_CHECK_RDB_BIN $dump_rdb --stats --format info
                    } result]

                    assert_equal 0 $failed
                    assert_match {*RDB looks OK!*} $result
                    assert_match {*\[logical offset *, physical offset *\] Logical RDB CRC64 skipped for streaming-compressed input*} $result
                    assert_match {*type.string.keys.total:1*} $result
                    assert_no_match {*Checksum OK*} $result
                } {
                    catch {r config set rdbcompression yes}
                }
            }
        }

        test "valkey-check-rdb rejects an incompatible VCS envelope" {
            r config set rdbcompression lz4
            set dir [lindex [r config get dir] 1]
            set incompatible_rdb [file join $dir incompatible-vcs.rdb]
            with_cleanup {
                r flushall
                r set lz4:incompatible payload
                r save

                set dump_rdb [file join $dir dump.rdb]
                set data [read_binary_file $dump_rdb]
                set data [string replace $data 3 3 [binary format c 2]]
                write_binary_file $incompatible_rdb $data

                set failed [catch {
                    exec $::VALKEY_CHECK_RDB_BIN $incompatible_rdb
                } result]

                assert_equal 1 $failed
                assert_match {*Invalid or unsupported RDB stream envelope*} $result
                assert_no_match {*RDB looks OK*} $result
            } {
                file delete -force $incompatible_rdb
                catch {r config set rdbcompression yes}
            }
        }

        foreach mode {lz4 zstd} {
            test "valkey-check-rdb rejects a [string toupper $mode]-compressed RDB with a truncated frame trailer" {
                if {$mode eq "zstd" && ![config_value_supported r rdbcompression zstd]} {
                    skip "zstd is not supported by this build"
                }

                r config set rdbcompression $mode
                set dir [lindex [r config get dir] 1]
                set truncated_rdb [file join $dir "truncated-$mode-vcs.rdb"]
                with_cleanup {
                    r flushall
                    r set "$mode:truncated" [string repeat "payload " 200]
                    r save

                    set dump_rdb [file join $dir dump.rdb]
                    set data [read_binary_file $dump_rdb]
                    write_binary_file $truncated_rdb [string range $data 0 end-1]

                    set failed [catch {
                        exec $::VALKEY_CHECK_RDB_BIN $truncated_rdb
                    } result]

                    assert_equal 1 $failed
                    assert_match {*\[logical offset *, physical offset *\] Compressed RDB stream did not end cleanly*} $result
                    assert_no_match {*RDB looks OK*} $result
                } {
                    file delete -force $truncated_rdb
                    catch {r config set rdbcompression yes}
                }
            }
        }

        test "valkey-check-rdb rejects a compressed RDB truncated mid-frame" {
            r config set rdbcompression lz4
            set dir [lindex [r config get dir] 1]
            set midframe_rdb [file join $dir midframe-vcs.rdb]
            with_cleanup {
                r flushall
                r set lz4:midframe [string repeat "payload " 200]
                r save

                set dump_rdb [file join $dir dump.rdb]
                set data [read_binary_file $dump_rdb]
                # Cut mid-frame rather than dropping the trailer: a file has no
                # more bytes coming, so this is corruption.
                set keep [expr {[string length $data] * 6 / 10}]
                write_binary_file $midframe_rdb [string range $data 0 [expr {$keep - 1}]]

                set failed [catch {
                    exec $::VALKEY_CHECK_RDB_BIN $midframe_rdb
                } result]

                assert_equal 1 $failed
                assert_match {*Corrupt compressed RDB stream*} $result
                assert_no_match {*RDB looks OK*} $result
            } {
                file delete -force $midframe_rdb
                catch {r config set rdbcompression yes}
            }
        }

        test "valkey-check-rdb ignores trailing data after a compressed RDB" {
            r config set rdbcompression lz4
            set dir [lindex [r config get dir] 1]
            set trailing_rdb [file join $dir trailing-vcs.rdb]
            with_cleanup {
                r flushall
                r set lz4:trailing payload
                r save

                set dump_rdb [file join $dir dump.rdb]
                set data [read_binary_file $dump_rdb]
                write_binary_file $trailing_rdb "${data}trailing-data"

                set failed [catch {
                    exec $::VALKEY_CHECK_RDB_BIN $trailing_rdb
                } result]

                assert_equal 0 $failed
                assert_match {*RDB looks OK*} $result
            } {
                file delete -force $trailing_rdb
                catch {r config set rdbcompression yes}
            }
        }

        test "valkey-check-rdb rejects corruption in a compressed RDB stream" {
            set dir [lindex [r config get dir] 1]
            set corrupt_rdb [file join $dir corrupt-vcs.rdb]
            r config set rdbcompression lz4
            with_cleanup {
                r flushall
                for {set i 0} {$i < 100} {incr i} {
                    r set "lz4:corrupt:$i" [string repeat "payload-$i " 100]
                }
                r save

                set dump_rdb [file join $dir dump.rdb]
                set data [read_binary_file $dump_rdb]
                set offset [expr {[string length $data] / 2}]
                binary scan [string index $data $offset] cu value
                set data [string replace $data $offset $offset [binary format c [expr {$value ^ 1}]]]

                write_binary_file $corrupt_rdb $data
                set failed [catch {
                    exec $::VALKEY_CHECK_RDB_BIN $corrupt_rdb
                } result]

                assert_equal 1 $failed
                assert_match {*Corrupt compressed RDB stream*} $result
                assert_no_match {*RDB looks OK*} $result
            } {
                file delete -force $corrupt_rdb
                catch {r config set rdbcompression yes}
            }
        }

        test "test valkey-check-rdb stats with empty RDB" {
            r flushall
            r save
            set dump_rdb [file join [lindex [r config get dir] 1] dump.rdb]
            catch {
                exec $::VALKEY_CHECK_RDB_BIN $dump_rdb --stats --format info
            } result
            assert_match "*db.0.type.string.keys.total:0*" $result
            assert_match "*db.0.type.list.keys.total:0*" $result
            assert_match "*db.0.type.set.keys.total:0*" $result
            assert_match "*db.0.type.zset.keys.total:0*" $result
            assert_match "*db.0.type.hash.keys.total:0*" $result
            assert_match "*db.0.type.stream.keys.total:0*" $result
        }

        test "test valkey-check-rdb stats function" {
            set function_num 11
            for {set i 0} {$i < $function_num} {incr i} {
                r function load [get_function_code LUA "test_$i" "test_$i" {return '$i'}]
            }
            r save
            
            set dump_rdb [file join [lindex [r config get dir] 1] dump.rdb]
            catch {
                exec $::VALKEY_CHECK_RDB_BIN $dump_rdb
            } result
            assert_match "*$function_num functions*" $result
        }

        test "test valkey-check-rdb stats key space" {
            r select 0
            for {set i 10} {$i < 20} {incr i} {
                set key [string repeat "$i" 10]
                set value [string repeat "$i" 100]
                r set $key $value
            }
            r select 1
            for {set i 20} {$i < 30} {incr i} {
                set key [string repeat "$i" 10]
                for {set j 0} {$j < 5} {incr j} {
                    r lpush $key [string repeat "$i" 100]
                }
            }
            r select 2
            for {set i 30} {$i < 40} {incr i} {
                set key [string repeat "$i" 10]
                for {set j 10} {$j < 20} {incr j} {
                    r sadd $key [string repeat "$j" 100]
                }
            }
            r select 3
            for {set i 40} {$i < 50} {incr i} {
                set key [string repeat "$i" 10]
                for {set j 10} {$j < 20} {incr j} {
                    set score $j
                    set member [string repeat "$j" 100]
                    r zadd $key $score $member
                }
            }
            r select 4
            for {set i 50} {$i < 60} {incr i} {
                set key [string repeat "$i" 10]
                for {set j 10} {$j < 20} {incr j} {
                    set field [string repeat "$j" 10]
                    set field_value [string repeat "$j" 10]
                    r hset $key $field $field_value
                }
            }
            r select 5
            for {set i 60} {$i < 70} {incr i} {
                set key [string repeat "$i" 10]
                for {set j 10} {$j < 20} {incr j} {
                    set field [string repeat "$j" 10]
                    set field_value [string repeat "$j" 10]
                    r xadd $key * $field $field_value
                }
            }
            r save
            
            set dump_rdb [file join [lindex [r config get dir] 1] dump.rdb]
            catch {
                exec $::VALKEY_CHECK_RDB_BIN $dump_rdb --stats --format info
            } result

            assert_match "*db.0.type.string.keys.total:10*" $result
            assert_match "*db.1.type.list.keys.total:10*" $result
            assert_match "*db.2.type.set.keys.total:10*" $result
            assert_match "*db.3.type.zset.keys.total:10*" $result
            assert_match "*db.4.type.hash.keys.total:10*" $result
            assert_match "*db.5.type.stream.keys.total:10*" $result
        }
    }
}

tags {"check-rdb network external:skip logreqres:skip"} {
    start_server {overrides {save "" rdbchecksum no}} {
        test "valkey-check-rdb accepts compressed RDBs created with rdbchecksum no" {
            r flushall
            r config set rdbcompression lz4
            r set lz4:no-cksum [string repeat "payload " 200]
            r save

            set dump_rdb [file join [lindex [r config get dir] 1] dump.rdb]
            set failed [catch {
                exec $::VALKEY_CHECK_RDB_BIN $dump_rdb
            } result]
            assert_equal 0 $failed
            assert_match {*Logical RDB CRC64 skipped for streaming-compressed input*} $result
            assert_match {*RDB looks OK!*} $result
            assert_no_match {*Checksum OK*} $result
        }
    }
}

tags {"check-rdb network external:skip logreqres:skip"} {
    start_server {overrides {save "" forkless-infrastructure-enabled yes forkless-policy prefer-forkless repl-diskless-sync yes repl-diskless-sync-delay 0}} {
        set primary [srv 0 client]
        set primary_host [srv 0 host]
        set primary_port [srv 0 port]

        for {set i 0} {$i < 100} {incr i} {
            $primary set init:$i val:$i
        }
        $primary config set rdb-key-save-delay 20000

        start_server {overrides {save "" repl-diskless-load disabled}} {
            set replica [srv 0 client]

            test "valkey-check-rdb accepts a replica dump.rdb containing opcode 242" {
                set loglines [count_log_lines -1]
                $replica replicaof $primary_host $primary_port
                wait_for_condition 100 20 {
                    [s -1 rdb_bgsave_in_progress] == 1
                } else {
                    fail "Forkless sync save did not start"
                }

                # Give the main-thread feeder one tick to queue the initial keys
                # so overwriting them emits inline RDB_OPCODE_UPDATE (0xF2) commands.
                after 50
                for {set i 0} {$i < 20} {incr i} {
                    $primary set init:$i updated:$i
                }
                $primary config set rdb-key-save-delay 0

                wait_for_sync $replica
                waitForBgsave $primary
                wait_for_log_messages -1 {"*Starting BGSAVE for SYNC with target: replicas sockets*method: forkless*"} $loglines 50 20

                set dump_rdb [server_rdb_path $replica]
                set data [read_binary_file $dump_rdb]
                set update_pos [string first "\xf2*3\r\n\$3\r\n" $data]
                assert {$update_pos != -1}

                set failed [catch {
                    exec $::VALKEY_CHECK_RDB_BIN $dump_rdb --stats --format info
                } result]
                assert_equal 0 $failed
                assert_match {*Checksum OK*} $result
                assert_match {*RDB looks OK!*} $result

                # Corrupting the RESP framing of an inline command in dump.rdb is rejected.
                set corrupt_frame_rdb [tmpfile check-rdb-242-corrupt-frame.rdb]
                binary scan [string index $data [expr {$update_pos + 1}]] cu orig_prefix_byte
                set corrupt_frame_data [string replace $data [expr {$update_pos + 1}] [expr {$update_pos + 1}] [binary format c [expr {$orig_prefix_byte ^ 1}]]]
                write_binary_file $corrupt_frame_rdb $corrupt_frame_data
                set failed [catch {exec $::VALKEY_CHECK_RDB_BIN $corrupt_frame_rdb} result]
                assert_equal 1 $failed
                assert_match {*Malformed inline replication command in RDB*} $result
                assert_no_match {*RDB looks OK*} $result

                # Corrupting a payload byte inside an inline command keeps framing valid
                # and is caught by the trailing RDB CRC check.
                set corrupt_crc_rdb [tmpfile check-rdb-242-corrupt-crc.rdb]
                binary scan [string index $data [expr {$update_pos + 9}]] cu orig_payload_byte
                set corrupt_crc_data [string replace $data [expr {$update_pos + 9}] [expr {$update_pos + 9}] [binary format c [expr {$orig_payload_byte ^ 1}]]]
                write_binary_file $corrupt_crc_rdb $corrupt_crc_data
                set failed [catch {exec $::VALKEY_CHECK_RDB_BIN $corrupt_crc_rdb} result]
                assert_equal 1 $failed
                assert_match {*RDB CRC error*} $result
                assert_no_match {*RDB looks OK*} $result
            } {} {needs:debug}
        }
    }

    start_server {overrides {save ""}} {
        r set k v
        r save
        set base_data [read_binary_file [server_rdb_path r]]
        set prefix [string range $base_data 0 end-9]
        set zero_tail "\xff\x00\x00\x00\x00\x00\x00\x00\x00"

        test "valkey-check-rdb rejects malformed and truncated opcode 242 frames" {
            # Non-array RESP prefix after opcode 242.
            set bad_prefix_rdb [tmpfile check-rdb-242-bad-prefix.rdb]
            write_binary_file $bad_prefix_rdb "$prefix\xf2+OK\r\n$zero_tail"
            set failed [catch {exec $::VALKEY_CHECK_RDB_BIN $bad_prefix_rdb} result]
            assert_equal 1 $failed
            assert_match {*Malformed inline replication command in RDB*} $result
            assert_match {*While doing: read-inline-cmd*} $result
            assert_no_match {*RDB looks OK*} $result

            # Corrupted bulk string terminator (not \r\n).
            set bad_crlf_rdb [tmpfile check-rdb-242-bad-crlf.rdb]
            write_binary_file $bad_crlf_rdb "$prefix\xf2*3\r\n\$3\r\nSET\r\n\$1\r\nk\r\n\$3\r\nbadXX$zero_tail"
            set failed [catch {exec $::VALKEY_CHECK_RDB_BIN $bad_crlf_rdb} result]
            assert_equal 1 $failed
            assert_match {*Malformed inline replication command in RDB*} $result
            assert_no_match {*RDB looks OK*} $result

            # Truncated mid-argument hitting EOF.
            set truncated_rdb [tmpfile check-rdb-242-truncated.rdb]
            write_binary_file $truncated_rdb "$prefix\xf2*3\r\n\$3\r\nSET\r\n\$10\r\nshort"
            set failed [catch {exec $::VALKEY_CHECK_RDB_BIN $truncated_rdb} result]
            assert_equal 1 $failed
            assert_match {*Unexpected EOF reading RDB file*} $result
            assert_match {*While doing: read-inline-cmd*} $result
            assert_no_match {*RDB looks OK*} $result

            # Opcode 242 in an RDB version older than 81 or a foreign REDIS header.
            set old_ver_rdb [tmpfile check-rdb-242-old-ver.rdb]
            set inline "\xf2*3\r\n\$3\r\nSET\r\n\$1\r\nk\r\n\$1\r\nv\r\n"
            write_binary_file $old_ver_rdb "VALKEY080[string range $prefix 9 end]$inline$zero_tail"
            set failed [catch {exec $::VALKEY_CHECK_RDB_BIN $old_ver_rdb} result]
            assert_equal 1 $failed
            assert_match {*Opcode 242 requires RDB version 81 or newer*} $result
            assert_no_match {*RDB looks OK*} $result

            set foreign_rdb [tmpfile check-rdb-242-foreign.rdb]
            write_binary_file $foreign_rdb "REDIS0012[string range $prefix 9 end]$inline$zero_tail"
            set failed [catch {exec $::VALKEY_CHECK_RDB_BIN $foreign_rdb} result]
            assert_equal 1 $failed
            assert_match {*Unknown object type 242 in RDB file with foreign version 12*} $result
            assert_no_match {*RDB looks OK*} $result
        }
    }
}
