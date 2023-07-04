-------------------------------- MODULE Move --------------------------------
EXTENDS TLC, Naturals, Sequences, Integers, FiniteSets

CONSTANTS Time, Nodes, Meta, MaxNodes, Root, NULL

\* Maybe Old Parent
OldParentStates == [
                     type: {"noExist", "yesExist"},
                     view : << Nodes, Meta >>
                   ]

LogMove == Time \X OldParentStates \X Nodes \X Meta \X Nodes

Move == Time \X Nodes \X Meta \X Nodes

\* (parent, meta, child) в root положить module value вместо parent и child
TreeNode == Nodes \X Meta \X Nodes

\* (’t, ’n, ’m) state =〈 (’t, ’n, ’m) log_op list × (’n × ’m × ’n) set 〉
\* Sets are collections of unordered, unique values.
\* State == << Seq(LogMove), Seq(TreeNode) >>

(***************************************************************************)
(* The spec is a straightforward TLA+ spec of the algorithm described      *)
(* above.                                                                  *)
(***************************************************************************)
VARIABLES
  logMove, \* log_op list (’t, ’n, ’m)
  treeSet \* set of edges (parent, meta, child).
  
 
vars == <<logMove, treeSet>>

TypeOK == /\ logMove \in SUBSET(LogMove)
          /\ treeSet \in SUBSET(TreeNode)

Init ==  /\ logMove = {}
         /\ treeSet = {}

\* (’t, ’n, ’m) log_op × (’n × ’m × ’n) set ⇒ (’n × ’m × ’n) set
undoOp(logMoveOp) ==
  /\ logMoveOp \in LogMove
  /\ LET t    == logMoveOp[1]
         ops  == logMoveOp[2]
         newp == logMoveOp[3]
         m    == logMoveOp[4]
         c    == logMoveOp[5]
     IN  \/ /\ ops.type = "noExist"
            /\ treeSet' = [<<p1, m1, c1>> \in treeSet |-> c /= c1]
            /\ UNCHANGED <<logMove>>
         \/ /\ ops.type = "yesExist"
            /\ LET oldp == ops[2][1]
                   oldm == ops[2][2]
               IN /\ treeSet' = [<<p1, m1, c1>> \in treeSet |-> c /= c1] \union <<oldp, oldm, c>>
                  /\ UNCHANGED <<logMove>>

\* 〈 (’n × ’m × ’n) set ⇒ ’n ⇒ (’n × ’m) option 
getParent(tree, child) ==
  /\ tree  \in Seq(TreeNode)
  /\ child \in Nodes
  /\ \/ LET x      == CHOOSE <<p1, m1, c1>> \in tree: c1 = child \* TODO это все упадает в модельки переписать на фильтр
            parent == x[1]
            meta   == x[2]
        IN [type : "yesExist", view : <<parent, meta>>]
     \/ [type : "noExist", view : <<{}, {}>>] \* поменять на null

\*  (’n × ’m × ’n) set ⇒ ’n ⇒ ’n ⇒ bool
RECURSIVE ancestor
ancestor == 
  [tree \in SUBSET(TreeNode), parent \in Nodes, child  \in Nodes |-> 
    \/ Cardinality({<<p1, m1, c1>> \in tree : p1 = parent /\ c1 = child}) # 0
    \/ \E <<p2, m2, c2>> \in tree: {<<p1, m1, c1>> \in tree: ancestor[tree, parent, p2] /\ c1 = c2}
  ]


\* 〈 (’t, ’n, ’m) operation × (’n × ’m × ’n) set ⇒ (’t, ’n, ’m) log_op × (’n × ’m × ’n) set 〉
doOp(moveOp) ==
  /\ moveOp \in Move
  /\ LET t    == moveOp[1]
         newp == moveOp[2]
         m    == moveOp[3]
         c    == moveOp[4]
         getParent1 == getParent(treeSet, c)
     IN /\ IF ancestor[treeSet, c, newp] \/ c = newp 
           THEN /\ UNCHANGED <<logMove, treeSet>>
           ELSE /\ treeSet' = [<<p1, m1, c1>> \in treeSet |-> c1 /= c] \union {<<newp, m, c>>}
                /\ UNCHANGED <<logMove>>
        /\ <<t, getParent1, newp, m, c>>

\* (’t, ’n, ’m) log_op ⇒ (’t, ’n, ’m) operation
logMoveToMove(logMoveOp) ==
  /\ logMoveOp \in LogMove
  /\ LET t == logMoveOp[1]
         p == logMoveOp[3]
         m == logMoveOp[4]
         c == logMoveOp[5]
     IN <<t, p, m, c>>

\* (’t, ’n, ’m) log_op ⇒ (’t, ’n, ’m) state ⇒ (’t, ’n, ’m) state
redoOp(logMoveOp) ==
  /\ logMoveOp \in LogMove
  /\ LET move  == logMoveToMove(logMoveOp)
         op2   == doOp (move)
     IN /\ logMove' = op2 \o logMove
        /\ UNCHANGED <<treeSet>>

\* (’t::{linorder}, ’n, ’m) operation ⇒ (’t, ’n, ’m) state ⇒ (’t, ’n, ’m) state 〉
RECURSIVE applyOp(_)
applyOp(moveOp) ==
  /\ moveOp \in Move
  /\ IF logMove = <<>>
     THEN LET op2 == doOp(moveOp)
          IN /\ logMove' = op2 \o logMove
             /\ treeSet' = treeSet
     ELSE
        LET logop == Head(logMove)
            ops   == Tail(logMove)
        IN IF moveOp[1] < logop[1] 
           THEN /\ logMove' = ops
                /\ treeSet' = undoOp(logop)
                /\ applyOp(moveOp) \* хз можно нарушить абстракцию и попытаться с оптимизировать, 
                                   \* чтобы не делать лишний redoOp когда нас реджекнули в doOp 
                                   \* и затем пришелдний из рекурсивного applyOp 
                /\ redoOp(logop)
           ELSE LET op2 == doOp (moveOp)
                IN /\ logMove' = op2 \o logop \o ops
                   /\ UNCHANGED <<treeSet>>

Next == \E move \in Move: applyOp(move) \* поставить 

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Tue Jul 04 16:42:39 MSK 2023 by ilyabarishnikov
\* Created Mon Apl 24 15:34:01 MSK 2023 by ilyabarishnikov
