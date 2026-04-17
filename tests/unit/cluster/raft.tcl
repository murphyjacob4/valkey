# Targeted tests for Cluster Raft membership and joining.

tags {tls:skip external:skip cluster singledb} {

set base_conf [list cluster-enabled yes cluster-raft-enabled yes]
start_multiple_servers 3 [list overrides $base_conf] {

test "Nodes boot as single-member Raft groups" {
    for {set id 0} {$id < [llength $::servers]} {incr id} {
        # In Raft mode, nodes should only know themselves initially.
        assert {[CI $id cluster_known_nodes] eq 1}
    }
}

test "CLUSTER MEET merges groups" {
    # Meet node 0 with node 1
    set b_port [srv -1 port]
    R 0 cluster meet 127.0.0.1 $b_port
    
    # Wait for they to see each other and form a group of 2
    wait_for_condition 100 50 {
        [CI 0 cluster_known_nodes] eq 2 && [CI 1 cluster_known_nodes] eq 2 &&
        [CI 0 raft_role] ne "joining" && [CI 1 raft_role] ne "joining" &&
        [CI 0 raft_leader] eq [CI 1 raft_leader] &&
        ([CI 0 raft_leader] eq [CI 0 raft_node_id] || [CI 0 raft_leader] eq [CI 1 raft_node_id])
    } else {
        puts "Node 0 knows: [CI 0 cluster_known_nodes] nodes, role: [CI 0 raft_role], leader: [CI 0 raft_leader]"
        puts "Node 1 knows: [CI 1 cluster_known_nodes] nodes, role: [CI 1 raft_role], leader: [CI 1 raft_leader]"
        fail "Nodes failed to join into a 2-node cluster"
    }
    
    # Now meet node 1 with node 2
    set c_port [srv -2 port]
    R 1 cluster meet 127.0.0.1 $c_port
    
    # Wait for all 3 to join
    wait_for_condition 100 50 {
        [CI 0 cluster_known_nodes] eq 3 && [CI 1 cluster_known_nodes] eq 3 && [CI 2 cluster_known_nodes] eq 3 &&
        [CI 0 raft_leader] eq [CI 1 raft_leader] && [CI 0 raft_leader] eq [CI 2 raft_leader]
    } else {
        fail "Nodes failed to join into a 3-node cluster"
    }
}

if {0} {
    test "CLUSTER FORGET removes a node" {
        # Find the leader
        set leader_id -1
        for {set id 0} {$id < 3} {incr id} {
            if {[CI $id raft_role] eq "leader"} {
                set leader_id $id
                break
            }
        }
        assert {$leader_id != -1}
        
        # Find a follower to forget
        set follower_id -1
        for {set id 0} {$id < 3} {incr id} {
            if {$id != $leader_id} {
                set follower_id $id
                break
            }
        }
        assert {$follower_id != -1}
        
        # Get the node ID of the follower
        set follower_node_id ""
        set lines [split [R $follower_id cluster nodes] "\n"]
        foreach line $lines {
            if {[string match "*myself*" $line]} {
                set follower_node_id [lindex [split $line " "] 0]
                break
            }
        }
        assert {$follower_node_id != ""}
        
        # Call FORGET on the leader
        R $leader_id cluster forget $follower_node_id
        
        # Wait for the cluster size to decrease to 2 on the leader
        wait_for_condition 5000 50 {
            [CI $leader_id cluster_known_nodes] eq 2
        } else {
            fail "Leader failed to forget the node"
        }
    }
}

} ;# stop servers

} ;# tags
