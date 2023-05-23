-------------------------------- MODULE Move --------------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets

(***************************************************************************)
(* We represent the graph by a set of Nodes of nodes and a set Edges of    *)
(* edges.  We assume that there are no edges from a node to itself and     *)
(* there is at most one edge joining any two nodes.  We represent an edge  *)
(* joining nodes m and n by the set {m, n}.  We let Root be the root node. *)
(***************************************************************************)
CONSTANTS Nodes, Edges, Meta, Time

(***************************************************************************)
(* This assumption asserts mathematically what we are assuming about the   *)
(* constants.                                                              *)
(***************************************************************************)
ASSUME \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)

(***************************************************************************)
(* This defines Nbrs(n) to be the set of neighbors of node n in the        *)
(* graph--that is, the set of nodes joined by an edge to n.                *)
(***************************************************************************)
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

\* Maybe Old Parent
OldParentStates == [
                     type: {"noExistParent", "existParent"},
                     view : << Nodes, Meta >>
                   ]
(*
datatype (’t, ’n, ’m) operation
    = Move (move_time:   ’t) 
           (move_parent: ’n) 
           (move_meta:   ’m) 
           (move_child:  ’n)
*)
Move == <<Time, Nodes, Meta, Nodes>>

(*
datatype (’t, ’n, ’m) log_op
    = LogMove (log_time:   ’t) 
              (old_parent: 〈 (’n × ’m) option 〉) 
              (new_parent: ’n) 
              (log_meta:   ’m) 
              (log_child:  ’n)
*)
LogMove == <<Time, OldParentStates, Nodes, Meta, Nodes>>

\* (parent, meta, child)
TreeNode == <<Nodes, Meta, Nodes>>

\* (’t, ’n, ’m) state =〈 (’t, ’n, ’m) log_op list × (’n × ’m × ’n) set 〉
State == << Seq(LogMove), Seq(TreeNode) >>

(***************************************************************************)
(* The spec is a straightforward TLA+ spec of the algorithm described      *)
(* above.                                                                  *)
(***************************************************************************)  
VARIABLES 
  treeSet, \* set of edges (parent, meta, child).
  logMove  \* log_op list (’t, ’n, ’m)
 
vars == <<treeSet, logMove>>

TypeOK == /\ treeSet \in Seq(TreeNode)
          /\ logMove \in Seq(LogMove)

\* {x \in S : p}

(* Move / Delete / Create *)

\* treeSet = {}, logMove = {}
Init ==  /\ treeSet = {}
         /\ logMove = {}

Next == {} \*


=============================================================================
\* Modification History
\* Last modified Tue May 23 16:46:43 MSK 2023 by ilyabarishnikov
\* Created Mon Apr 24 15:34:01 MSK 2023 by ilyabarishnikov
