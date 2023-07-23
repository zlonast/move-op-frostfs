-------------------------------- MODULE Move --------------------------------  
EXTENDS TLC, Naturals, Sequences, Integers, FiniteSets

CONSTANTS Time, Node, Meta, RootNode, TrashNode, Null, MaxSteps, MaxWorkers

Nodes == Node \union {RootNode} \union {TrashNode}
Workers == 1..MaxWorkers

(***************************************************************************)
(* The spec is a straightforward TLA+ spec of the algorithm described      *)
(* above.                                                                  *)
(***************************************************************************)
VARIABLES
  logMove,  \* log_op list (’t, ’n, ’m)
  treeSet,  \* set of edges (parent, meta, child)
  queue,    \* пусть у каждого будет своя очередь запросов с Move
  localTime \* локальное время для каждого из потоков

vars == <<logMove, treeSet, queue, localTime>>

\* хз можно нарушить абстракцию и попытаться с оптимизировать, 
\* чтобы не делать лишний redoOp когда нас реджекнули в doOp 
\* и затем пришелдний из рекурсивного applyOp

(* --------------------------Types---------------------------------------- *)

OldParentStates == [oldp : Nodes, oldm : Meta] \union {Null}

LogMove == [log_time : Time, old_parent : OldParentStates, new_parent : Nodes, log_meta : Meta, log_child : Nodes]

Move == [move_time : Time, move_parent : Nodes, move_meta : Meta, move_child : Nodes]

TreeNode == [parent : Nodes, meta : Meta, child : Nodes]

TypeOK == /\ logMove   \in [Workers -> Seq(LogMove)]
          /\ treeSet   \in [Workers -> SUBSET(TreeNode)]
          /\ queue     \in [Workers -> Seq(Move)]
          /\ localTime \in [Workers -> Time]

Init == /\ logMove   = [self \in Workers |-> <<>>]
        /\ treeSet   = [self \in Workers |-> {}]
        /\ queue     = [self \in Workers |-> <<>>]
        /\ localTime = [self \in Workers |-> 0]

(* -------------------------FUNCTIONS------------------------------------ *)

RECURSIVE findAllTreeNodes
findAllTreeNodes[tree \in SUBSET(TreeNode), node \in Nodes] ==
  LET childs == {edge \in tree: edge.parent = node}
      maps   == UNION {findAllTreeNodes[tree, edge.child] : edge \in childs}
  IN maps \union childs

RECURSIVE ancestor
ancestor[tree \in SUBSET(TreeNode), parent \in Nodes, child \in Nodes] ==
  \/ Cardinality({edge \in tree : edge.parent = parent /\ edge.child = child}) = 1
  \/ IF child = RootNode \/ Cardinality({edge \in tree : edge.child = child}) = 0
     THEN FALSE
     ELSE LET edgeChild == CHOOSE edge \in tree: edge.child = child
          IN ancestor[tree, parent, edgeChild.parent]

getParent[tree \in SUBSET(TreeNode), child \in Nodes] ==
  IF Cardinality({edge \in tree: edge.child = child}) = 1 \* стоит сделать инвариант на то что у каждого child один parent
  THEN LET edge == CHOOSE edge \in tree: edge.child = child
       IN [oldp |-> edge.parent, oldm |-> edge.meta]
  ELSE Null

logMoveToMove[log \in LogMove] ==
  [move_time : log.log_time, move_parent : log.new_parent, move_meta : log.log_meta, move_child : log.log_child]

moveToLogMove[self \in Workers, move \in Move] ==
  [log_time   |-> move.move_time,
   old_parent |-> getParent[treeSet[self], move.move_child],
   new_parent |-> move.move_parent, 
   log_meta   |-> move.move_meta, 
   log_child  |-> move.move_child]

SendMove(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ queue' = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
  /\ localTime' = [localTime EXCEPT ![self] = localTime[self] + 1]

SetNodes[tree \in SUBSET(TreeNode)] ==
  {edge.child: edge \in tree}

(* -----------------------SINGLE------------------------------------------ *)

AppendE(self) ==
  /\ self \in Workers
  /\ \E parent \in (SetNodes[treeSet[self]] \union {RootNode}): \* странно ощущается что всегд выбиратся RootNode
     LET child    == localTime[self] * 10 + self
         treeNode == [parent |-> parent, meta |-> 0, child |-> child]
         move     == [move_time   |-> localTime[self] * 10 + self,
                      move_parent |-> treeNode.parent,
                      move_meta   |-> treeNode.meta,
                      move_child  |-> treeNode.child]
     IN /\ treeSet'   = [treeSet EXCEPT ![self] = treeSet[self] \union {treeNode}]
        /\ SendMove(self, move)
  /\ UNCHANGED <<logMove>>

RemoveE(self) ==
  /\ self \in Workers
  /\ IF treeSet[self] = {}
     THEN UNCHANGED <<treeSet, queue, localTime>>
     ELSE \E edge \in treeSet[self]:
          LET treeNodes == findAllTreeNodes[treeSet[self], edge.child] \union {edge}
              move      == [move_time   |-> localTime[self] * 10 + self,
                            move_parent |-> TrashNode,
                            move_meta   |-> edge.meta,
                            move_child  |-> edge.child]
          IN /\ treeSet'   = [treeSet EXCEPT ![self] = treeSet[self] \ treeNodes]
             /\ SendMove(self, move)
  /\ UNCHANGED <<logMove>>

MoveE(self) ==
  /\ self \in Workers
  /\ IF treeSet[self] = {}
     THEN UNCHANGED <<treeSet, queue, localTime>>
     ELSE \E nodeChild \in SetNodes[treeSet[self]], nodeParent \in SetNodes[treeSet[self]]: 
          /\ nodeChild /= nodeParent
          /\ ancestor[treeSet[self], nodeChild, nodeParent] = FALSE
          /\ LET edgeChild == CHOOSE edge \in treeSet[self]: edge.child = nodeChild
                 treeNode  == [parent |-> nodeParent, meta |-> edgeChild.meta, child |-> nodeChild]
                 move      == [move_time   |-> localTime[self] * 10 + self,
                               move_parent |-> treeNode.parent,
                               move_meta   |-> treeNode.meta,
                               move_child  |-> treeNode.child]
             IN /\ treeSet'   = [treeSet EXCEPT ![self] = (treeSet[self] \ {edgeChild}) \union {treeNode}]
                /\ SendMove(self, move)
  /\ UNCHANGED <<logMove>>

(* -----------------------Apply------------------------------------------ *)

UndoOp(self, log) ==
  /\ self \in Workers
  /\ log \in LogMove
  /\ \/ /\ log.old_parent = Null
        /\ treeSet' = {edge \in treeSet[self]: log.log_child /= edge.child}
     \/ /\ log.old_parent # Null
        /\ LET treeNode == [parent |-> log.old_parent.oldp, meta |-> log.old_parent.oldm, child |-> log.log_child]
           IN treeSet' = [treeSet EXCEPT ![self] = {edge \in treeSet[self]: log.log_child /= edge.child} \union {treeNode}]

DoOp(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ IF ancestor[treeSet[self], move.move_child, move.move_parent] \/ move.move_child = move.move_parent 
     THEN UNCHANGED <<treeSet>>
     ELSE LET treeNode == [parent |-> move.move_parent, meta |-> move.move_meta, child |-> move.move_child]
          IN treeSet' = [treeSet EXCEPT ![self] = {edge \in treeSet[self]: edge.child /= move.move_child} \union {treeNode}]

RedoOp(self, log) ==
  /\ self \in Workers
  /\ log \in LogMove
  /\ DoOp (self, logMoveToMove[log])
  /\ LET op == moveToLogMove[self, logMoveToMove[log]]
     IN logMove' = [logMove EXCEPT ![self] = Append(logMove[self], op)]

RECURSIVE ApplyOp(_, _)
ApplyOp(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ IF logMove[self] = <<>>
     THEN LET op == moveToLogMove[self,move]
          IN /\ DoOp(self, move)
             /\ logMove' = [logMove EXCEPT ![self] = Append(logMove[self], op)]
     ELSE LET logop == Head(logMove[self])
              ops   == Tail(logMove[self])
          IN IF move.move_time < logop.log_time
             THEN /\ UndoOp(self, logop)
                  /\ logMove' = [logMove EXCEPT ![self] = ops]
                  /\ ApplyOp(self, move)
                  /\ RedoOp(self, logop)
             ELSE LET op == moveToLogMove[self,move]
                  IN /\ DoOp (self, move)
                     /\ logMove' = [logMove EXCEPT ![self] = Append(Append(ops, logop), op)]

TryApply(self) ==
  /\ queue[self] # <<>>
  /\ LET move  == Head(queue[self])
         moves == Tail(queue[self])
     IN /\ queue' = [queue EXCEPT ![self] = moves]
        /\ ApplyOp(self, move)
        /\ UNCHANGED <<localTime>>

(* -------------------------------------------------------------------------- *)

Next == \/ (\E self \in Workers: localTime[self] < MaxSteps /\ (AppendE(self) \/ RemoveE(self) \/ MoveE(self)))
        \/ (\E self \in Workers: TryApply(self))

FullStop == \A self \in Workers: localTime[self] = MaxSteps /\ queue[self] = <<>>

InvariantTree == IF FullStop THEN FALSE ELSE TRUE
\* инвариант что дерево в любой момент времени коректное
\* инвариант в конце концов они все придут к одному состоянию
\* инвариант что родитель всегда один

Spec == Init /\ [][Next]_vars \* /\ FullStop

THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Sun Jul 23 21:32:13 IRKT 2023 by ilyabarishnikov
\* Created Mon Apl 24 15:34:01 MSK 2023 by ilyabarishnikov
