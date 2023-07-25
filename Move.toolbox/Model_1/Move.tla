-------------------------------- MODULE Move --------------------------------  
EXTENDS TLC, Naturals, Sequences, Integers, FiniteSets

CONSTANTS Time, Node, MetaMax, RootNode, TrashNode, Null, MaxSteps, MaxWorkers

Nodes == Node \union {RootNode} \union {TrashNode}
Workers == 1..MaxWorkers
Meta == 1..MetaMax

(***************************************************************************)
(* The spec is a straightforward TLA+ spec of the algorithm described      *)
(* above.                                                                  *)
(***************************************************************************)
VARIABLES logMove, treeSet, queue

vars == <<logMove, treeSet, queue>>

(* -------------------------------- Types -------------------------------- *)

OldParentStates == [oldp : Nodes, oldm : Meta] \union {Null}

LogMove == [log_time : Time, old_parent : OldParentStates, new_parent : Nodes, log_meta : Meta, log_child : Nodes]

Move == [move_time : Time, move_parent : Nodes, move_meta : Meta, move_child : Nodes]

TreeNode == [parent : Nodes, meta : Meta, child : Nodes]

(* -------------------------------- FUNCTIONS -------------------------------- *)

RECURSIVE ancestor
ancestor[tree \in SUBSET(TreeNode), parent \in Nodes, child \in Nodes] ==
  \/ Cardinality({edge \in tree : edge.parent = parent /\ edge.child = child}) = 1
  \/ IF child = RootNode \/ Cardinality({edge \in tree : edge.child = child}) = 0
     THEN FALSE
     ELSE LET edgeChild == CHOOSE edge \in tree: edge.child = child
          IN ancestor[tree, parent, edgeChild.parent]

getParent[tree \in SUBSET(TreeNode), child \in Nodes] ==
  IF Cardinality({edge \in tree: edge.child = child}) = 1
  THEN LET edge == CHOOSE edge \in tree: edge.child = child
       IN [oldp |-> edge.parent, oldm |-> edge.meta]
  ELSE Null

SendMove(self, move, log) ==
  /\ self \in Workers
  /\ move \in Move
  /\ log  \in LogMove 
  /\ queue'   = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
  /\ logMove' = [logMove EXCEPT ![self] = <<log>> \o @]

SetNodes[tree \in SUBSET(TreeNode)] ==
  {edge.child: edge \in tree}

timeSelf[self \in Workers] == Len(logMove[self]) * MaxWorkers + self

moveToLogMove[move \in Move, tree \in SUBSET(TreeNode)] ==
  [log_time   |-> move.move_time,
   old_parent |-> getParent[tree, move.move_child],
   new_parent |-> move.move_parent,
   log_meta   |-> move.move_meta,
   log_child  |-> move.move_child]

logMoveToMove[log \in LogMove] ==
  [move_time   |-> log.log_time, 
   move_parent |-> log.new_parent, 
   move_meta   |-> log.log_meta,
   move_child  |-> log.log_child]

RECURSIVE findAllTreeNodes
findAllTreeNodes[tree \in SUBSET(TreeNode), node \in Nodes] ==
  LET childs == {edge \in tree: edge.parent = node}
      maps   == UNION {findAllTreeNodes[tree, edge.child] : edge \in childs}
  IN maps \union childs


(*************************************************************************)
(* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
(* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
(*************************************************************************)
ToSet(s) == { s[i] : i \in DOMAIN s }

(* -------------------------------- SINGLE -------------------------------- *)

AppendE(self) ==
  /\ self \in Workers
  /\ \E parent \in (SetNodes[treeSet[self]] \union {RootNode}), meta \in Meta:
     LET child    == timeSelf[self]
         treeNode == [parent |-> parent, meta |-> meta, child |-> child]
         move     == [move_time   |-> timeSelf[self],
                      move_parent |-> treeNode.parent,
                      move_meta   |-> treeNode.meta,
                      move_child  |-> treeNode.child]
         log      == [log_time   |-> move.move_time,
                      old_parent |-> Null,
                      new_parent |-> move.move_parent,
                      log_meta   |-> move.move_meta,
                      log_child  |-> move.move_child]
     IN /\ treeSet' = [treeSet EXCEPT ![self] = @ \union {treeNode}]
        /\ SendMove(self, move, log)

MoveE(self) ==
  /\ self \in Workers
  /\ treeSet[self] # {}
  /\ \E childCur \in SetNodes[treeSet[self]], parentNew \in (SetNodes[treeSet[self]] \union {TrashNode}), metaNew \in Meta:
     /\ childCur # parentNew
     /\ ancestor[treeSet[self], childCur, parentNew] = FALSE
     /\ LET edgeChild == CHOOSE edge \in treeSet[self]: edge.child = childCur
            treeNode  == [parent |-> parentNew, meta |-> metaNew, child |-> childCur]
            move      == [move_time   |-> timeSelf[self],
                          move_parent |-> treeNode.parent,
                          move_meta   |-> treeNode.meta,
                          move_child  |-> treeNode.child]
            log       == [log_time   |-> move.move_time,
                          old_parent |-> [oldp |-> edgeChild.parent, oldm |-> edgeChild.meta],
                          new_parent |-> move.move_parent,
                          log_meta   |-> move.move_meta,
                          log_child  |-> move.move_child]
         IN /\ treeSet' = [treeSet EXCEPT ![self] = (@ \ {edgeChild}) \union {treeNode}]
            /\ SendMove(self, move, log)

(* -------------------------------- Apply -------------------------------- *)

undoOp[log \in LogMove, tree \in SUBSET(TreeNode)] ==
  IF log.old_parent = Null
  THEN {edge \in tree: log.log_child # edge.child}
  ELSE LET treeNode == [parent |-> log.old_parent.oldp, meta |-> log.old_parent.oldm, child |-> log.log_child]
       IN {edge \in tree: log.log_child # edge.child} \union {treeNode}

doOp[move \in Move, tree \in SUBSET(TreeNode)] ==
  IF ancestor[tree, move.move_child, move.move_parent] \/ move.move_child = move.move_parent
  THEN tree
  ELSE LET treeNode == [parent |-> move.move_parent, meta |-> move.move_meta, child |-> move.move_child]
       IN {edge \in tree: move.move_child # edge.child} \union {treeNode}

RECURSIVE applyOp
applyOp[move \in Move, logs \in Seq(LogMove), tree \in SUBSET(TreeNode)] ==
  IF logs = <<>> /\ tree = {}
  THEN << <<moveToLogMove[move, {}]>>, doOp[move, {}] >>
  ELSE LET logop == Head(logs)
       IN IF move.move_time < logop.log_time
          THEN LET treeUndo == undoOp[logop, tree]
                   logsUndo == Tail(logs)
                   res      == applyOp[move, logsUndo, treeUndo]
                   moveDO   == logMoveToMove[logop]
                   treeDo   == doOp [moveDO, res[2]]
                   op       == moveToLogMove[moveDO, res[2]]
               IN << <<op>> \o res[1], treeDo >>
          ELSE LET treeDo == doOp [move, tree]
                   op     == moveToLogMove[move, tree]
               IN << <<op>> \o logs, treeDo >>

TryApply(self) ==
  /\ queue[self] # <<>>
  /\ LET move  == Head(queue[self])
         moves == Tail(queue[self])
         res   == applyOp[move, logMove[self], treeSet[self]]
     IN /\ queue'   = [queue   EXCEPT ![self] = moves]
        /\ logMove' = [logMove EXCEPT ![self] = res[1]]
        /\ treeSet' = [treeSet EXCEPT ![self] = res[2]]

(* ---------------------------------------------------------------- *)

Init == /\ logMove = [self \in Workers |-> <<>>]
        /\ treeSet = [self \in Workers |-> {}]
        /\ queue   = [self \in Workers |-> <<>>]

worker(self) == \/ (Len(logMove[self]) < MaxSteps /\ (AppendE(self) \/ MoveE(self)))
                \/ TryApply(self)

End == /\ \A self \in Workers: Len(logMove[self]) >= MaxSteps /\ queue[self] = <<>>
       /\ \A i, j \in Workers: treeSet[i] = treeSet[j]
       /\ \A i, j \in Workers: logMove[i] = logMove[j]

Terminating == End /\ UNCHANGED vars

Next == \/ (\E self \in Workers: worker(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Workers : WF_vars(worker(self))

(* -------------------------------- Invariants -------------------------------- *)

TypeOK == /\ logMove \in [Workers -> Seq(LogMove)]
          /\ treeSet \in [Workers -> SUBSET(TreeNode)]
          /\ queue   \in [Workers -> Seq(Move)]

OneParent == \A self \in Workers:
             \A child \in {edge.child: edge \in treeSet[self]}: 
             Cardinality({edge \in treeSet[self]: child = edge.child}) = 1

TwoBeginnings ==
  \A self \in Workers:
  LET rootTree  == findAllTreeNodes[treeSet[self], RootNode]
      trashTree == findAllTreeNodes[treeSet[self], TrashNode]
  IN (rootTree \union trashTree) = treeSet[self]

EmprtyLogAndTree == \A self \in Workers: logMove[self] = <<>> <=> treeSet[self] = {}

ModelConstSizeLogMove ==
  \A self \in Workers: 
  /\ 0 <= Len(logMove[self])
  /\ Len(logMove[self]) <= Cardinality(Workers) * MaxSteps

ModelConstSizeTreeSet ==
  \A self \in Workers:
  /\ 0 <= Cardinality(treeSet[self])
  /\ Cardinality(treeSet[self]) <= Cardinality(Workers) * MaxSteps

ModelConstSizeQueue ==
  \A self \in Workers:
  /\ 0 <= Len(queue[self])
  /\ Len(queue[self]) <= (Cardinality(Workers) - 1) * MaxSteps

(* -------------------------------- Properties -------------------------------- *)

\* для всего что попало в очередь, верно то что оно окажется в логе 

LivenessQueueToLogMove ==
  LET TimeConstant == 1..Cardinality(Workers) * MaxSteps
  IN \A self \in Workers:
       \A moveTime \in TimeConstant:
         Cardinality({move \in ToSet(queue[self]): move.move_time = moveTime}) = 1
           ~> \E logTime \in TimeConstant:
             /\ Cardinality({log \in ToSet(logMove[self]): log.log_time = logTime}) = 1
             /\ moveTime = logTime

PropEnd == <>[]End

THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Tue Jul 25 22:02:57 IRKT 2023 by ilyabarishnikov
\* Created Mon Apl 24 15:34:01 MSK 2023 by ilyabarishnikov
