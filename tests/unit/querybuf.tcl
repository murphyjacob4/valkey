proc client_idle_sec {name} {
    set clients [split [r client list] "\r\n"]
    set c [lsearch -inline $clients *name=$name*]
    assert {[regexp {idle=([0-9]+)} $c - idle]}
    return $idle
}

# Calculate query buffer memory of client
proc client_query_buffer {name} {
    set clients [split [r client list] "\r\n"]
    set c [lsearch -inline $clients *name=$name*]
    if {[string length $c] > 0} {
        assert {[regexp {qbuf=([0-9]+)} $c - qbuf]}
        assert {[regexp {qbuf-free=([0-9]+)} $c - qbuf_free]}
        return [expr $qbuf + $qbuf_free]
    }
    return 0
}

start_server {tags {"querybuf slow"}} {
    # increase the execution frequency of clientsCron
    r config set hz 100

    test "query buffer is only held while a command is pending" {
        set rd [valkey_deferring_client]

        $rd client setname test_client
        $rd read

        # Between commands the client holds no query buffer.
        assert {[client_query_buffer test_client] == 0}

        # Send a partial command so the client has to hold a query buffer.
        $rd write "*3\r\n\$3\r\nset\r\n\$2\r\na"
        $rd flush
        wait_for_condition 1000 10 {
            [client_query_buffer test_client] > 0
        } else {
            fail "client should hold a query buffer while a command is pending"
        }

        # Once the command completes, the buffer is returned to the pool right away,
        # without waiting for clientsCron.
        $rd write "a\r\n\$1\r\nb\r\n"
        $rd flush
        assert_equal {OK} [$rd read]
        assert {[client_query_buffer test_client] == 0}
        $rd close
    }

    test "query buffer is not retained after a large argument" {
        set rd [valkey_client]
        $rd client setname test_client

        # A large argument is read into a dedicated object, not the query buffer,
        # and nothing is retained once the command completes.
        $rd set x [string repeat A 400000]
        assert {[client_query_buffer test_client] == 0}
        assert_equal 400000 [r strlen x]

        $rd set x [string repeat A 100]
        assert {[client_query_buffer test_client] == 0}
        $rd close
    }

    test "query buffer resized correctly with fat argv" {
        set rd [valkey_client]
        $rd client setname test_client
        $rd write "*3\r\n\$3\r\nset\r\n\$1\r\na\r\n\$1000000\r\n"
        $rd flush
        
        after 200
        # Send the start of the arg and make sure the client is not using shared qb for it rather a private buf of > 1000000 size.
        $rd write "a" 
        $rd flush

        after 20
        if {[client_query_buffer test_client] < 1000000} {
            fail "query buffer should not be resized when client idle time smaller than 2s"
        }
     
        # Check that the query buffer is resized after 2 sec
        wait_for_condition 1000 10 {
            [client_idle_sec test_client] >= 3 && [client_query_buffer test_client] < 1000000
        } else {
            fail "query buffer should be resized when client idle time bigger than 2s"
        }

        # Finish the argument: the upload resumes and the stored value is intact.
        $rd write "[string repeat b 999998]c\r\n"
        $rd flush
        assert_equal {OK} [$rd read]
        assert_equal 1000000 [r strlen a]
        assert_equal "ab" [r getrange a 0 1]
        assert_equal "bc" [r getrange a 999998 999999]
        assert {[client_query_buffer test_client] == 0}

        $rd close
    }

}
