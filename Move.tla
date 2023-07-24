-------------------------------- MODULE Move --------------------------------  
EXTENDS TLC, Naturals, Sequences, Integers, FiniteSets

CONSTANTS Time, Node, RootNode, TrashNode, Null, MaxSteps, MaxWorkers

Nodes == Node \union {RootNode} \union {TrashNode}
Workers == 1..MaxWorkers

(***************************************************************************)
(* The spec is a straightforward TLA+ spec of the algorithm described      *)
(* above.                                                                  *)
(***************************************************************************)
VARIABLES logMove, treeSet, queue, localTime

vars == <<logMove, treeSet, queue, localTime>>

\* хз можно нарушить абстракцию и попытаться с оптимизировать, 
\* чтобы не делать лишний redoOp когда нас реджекнули в doOp 
\* и затем пришелдний из рекурсивного applyOp

(* -------------------------------- Types -------------------------------- *)

OldParentStates == [oldp : Nodes] \union {Null}

LogMove == [log_time : Time, old_parent : OldParentStates, new_parent : Nodes, log_child : Nodes]

Move == [move_time : Time, move_parent : Nodes, move_child : Nodes]

TreeNode == [parent : Nodes, child : Nodes]

(* -------------------------------- FUNCTIONS -------------------------------- *)

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
       IN [oldp |-> edge.parent]
  ELSE Null

logMoveToMove[log \in LogMove] ==
  [move_time : log.log_time, move_parent : log.new_parent, move_child : log.log_child]

moveToLogMove[self \in Workers, move \in Move] ==
  [log_time   |-> move.move_time,
   old_parent |-> getParent[treeSet[self], move.move_child],
   new_parent |-> move.move_parent,
   log_child  |-> move.move_child]

SendMove(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ queue' = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
  /\ localTime' = [localTime EXCEPT ![self] = @ + 1]

SetNodes[tree \in SUBSET(TreeNode)] ==
  {edge.child: edge \in tree}

timeSelf(self) == localTime[self] * MaxWorkers + self

(* -------------------------------- SINGLE -------------------------------- *)

AppendE(self) ==
  /\ self \in Workers
  /\ \E parent \in (SetNodes[treeSet[self]] \union {RootNode}):
     LET child    == timeSelf(self)
         treeNode == [parent |-> parent, child |-> child]
         move     == [move_time   |-> timeSelf(self),
                      move_parent |-> treeNode.parent,
                      move_child  |-> treeNode.child]
         log      == [log_time   |-> move.move_time,
                      old_parent |-> Null,
                      new_parent |-> move.move_parent,
                      log_child  |-> move.move_child]
     IN \* /\ logMove' = [logMove EXCEPT ![self] = Append(@, log)]
        /\ treeSet' = [treeSet EXCEPT ![self] = @ \union {treeNode}]
        /\ SendMove(self, move)
        /\ UNCHANGED <<logMove>>

MoveE(self) ==
  /\ self \in Workers
  /\ IF treeSet[self] = {}
     THEN UNCHANGED <<logMove, treeSet, queue, localTime>>
     ELSE \E nodeChild \in SetNodes[treeSet[self]], nodeParent \in (SetNodes[treeSet[self]] \union {TrashNode}):
          /\ nodeChild # nodeParent
          /\ ancestor[treeSet[self], nodeChild, nodeParent] = FALSE
          /\ LET edgeChild == CHOOSE edge \in treeSet[self]: edge.child = nodeChild
                 treeNode  == [parent |-> nodeParent, child |-> nodeChild]
                 move      == [move_time   |-> timeSelf(self),
                               move_parent |-> treeNode.parent,
                               move_child  |-> treeNode.child]
                 log       == [log_time   |-> move.move_time,
                               old_parent |-> [oldp |-> edgeChild.parent],
                               new_parent |-> move.move_parent,
                               log_child  |-> move.move_child]
             IN \* /\ logMove' = [logMove EXCEPT ![self] = Append(@, log)]
                /\ treeSet' = [treeSet EXCEPT ![self] = (@ \ {edgeChild}) \union {treeNode}]
                /\ SendMove(self, move)
                /\ UNCHANGED <<logMove>>

(* -------------------------------- Apply -------------------------------- *)

UndoOp(self, log) ==
  /\ self \in Workers
  /\ log \in LogMove
  /\ \/ /\ log.old_parent = Null
        /\ treeSet' = {edge \in treeSet[self]: log.log_child /= edge.child}
     \/ /\ log.old_parent # Null
        /\ LET treeNode == [parent |-> log.old_parent.oldp, child |-> log.log_child]
           IN treeSet' = [treeSet EXCEPT ![self] = {edge \in @: log.log_child /= edge.child} \union {treeNode}]

DoOp(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ IF ancestor[treeSet[self], move.move_child, move.move_parent] \/ move.move_child = move.move_parent
     THEN UNCHANGED <<treeSet>>
     ELSE LET treeNode == [parent |-> move.move_parent, child |-> move.move_child]
          IN treeSet' = [treeSet EXCEPT ![self] = {edge \in @: edge.child /= move.move_child} \union {treeNode}]

RedoOp(self, log) ==
  /\ self \in Workers
  /\ log \in LogMove
  /\ DoOp (self, logMoveToMove[log])
  /\ LET op == moveToLogMove[self, logMoveToMove[log]]
     IN logMove' = [logMove EXCEPT ![self] = Append(@, op)]

RECURSIVE ApplyOp(_, _)
ApplyOp(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ IF logMove[self] = <<>>
     THEN LET op == moveToLogMove[self, move]
          IN /\ DoOp(self, move)
             /\ logMove' = [logMove EXCEPT ![self] = Append(@, op)]
     ELSE LET logop == Head(logMove[self])
              ops   == Tail(logMove[self])
          IN IF move.move_time < logop.log_time
             THEN /\ UndoOp(self, logop)
                  /\ logMove' = [logMove EXCEPT ![self] = ops]
                  /\ ApplyOp(self, move)
                  /\ RedoOp(self, logop)
             ELSE LET op == moveToLogMove[self,move]
                  IN /\ DoOp (self, move)
                     /\ logMove' = [logMove EXCEPT ![self] = Append(@, op)]

TryApply(self) ==
  /\ queue[self] # <<>>
  /\ LET move  == Head(queue[self])
         moves == Tail(queue[self])
     IN /\ queue' = [queue EXCEPT ![self] = moves]
        /\ ApplyOp(self, move)
        /\ UNCHANGED <<localTime>>

(* ---------------------------------------------------------------- *)

Init == /\ logMove   = [self \in Workers |-> <<>>]
        /\ treeSet   = [self \in Workers |-> {}]
        /\ queue     = [self \in Workers |-> <<>>]
        /\ localTime = [self \in Workers |-> 0]

worker(self) == \/ (localTime[self] < MaxSteps /\ (AppendE(self) \/ MoveE(self)))
                \/ TryApply(self)

Terminating == /\ \A self \in Workers: localTime[self] = MaxSteps /\ queue[self] = <<>>
               /\ UNCHANGED vars

Next == \/ (\E self \in Workers: worker(self))
        \/ Terminating

\* []P => []Q
\* Safety == \E s \in Servers: [](s \in online)
\* []~P means that P is always not true
\* ~[]P means that P isn’t always true
\* In every behavior, there is at least one state where P is false
\* It's not the case that all servers are always online
\* Liveness == ~[](online = Servers)

\* <>P, or “Eventually P”
\* AllDone ==  \A t \in Threads: pc[t] = "Done"
\* Correct == AllDone => counter = NumThreads
\* Liveness == <>(counter = NumThreads)
\* (Remember this is checked under “Temporal Properties”, not “Invariants”!)

\* <>[]P is “eventually P is always true”
\* Liveness == <>[](counter = NumThreads)

\* A property of this system might be that every inbound task is eventually processed by a worker. 
\* Liveness == \A t \in TaskType: t \in inbound ~> \E w \in Workers: t \in worker_pool[w]

\* инвариант что дерево в любой момент времени коректное
\* свойство в конце концов они все придут к одному состоянию
\* инвариант что родитель всегда один

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Workers : WF_vars(worker(self))

(* -------------------------------- Invariants -------------------------------- *)

TypeOK == /\ logMove   \in [Workers -> Seq(LogMove)]
          /\ treeSet   \in [Workers -> SUBSET(TreeNode)]
          /\ queue     \in [Workers -> Seq(Move)]
          /\ localTime \in [Workers -> Time]

OneParent == \A self \in Workers:
             \A child \in {edge.child: edge \in treeSet[self]}: 
             Cardinality({edge \in treeSet[self]: child = edge.child}) = 1

TwoBeginnings ==
  LET RECURSIVE findAllTreeNodes
      findAllTreeNodes[tree \in SUBSET(TreeNode), node \in Nodes] ==
        LET childs == {edge \in tree: edge.parent = node}
             maps   == UNION {findAllTreeNodes[tree, edge.child] : edge \in childs}
        IN maps \union childs
  IN \A self \in Workers:
     LET rootTree  == findAllTreeNodes[treeSet[self], RootNode]
         trashTree == findAllTreeNodes[treeSet[self], TrashNode]
     IN (rootTree \union trashTree) = treeSet[self]


(* -------------------------------- Properties -------------------------------- *)

FullStop == <>[](\A self \in Workers: localTime[self] = MaxSteps /\ queue[self] = <<>>)

OneTreeEnd == <>[](\A i, j \in Workers: treeSet[i] = treeSet[j])

OneLogMoveEnd == <>[](\A i, j \in Workers: logMove[i] = logMove[j])

(*
мне нужны юнит тесты
*)

THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Mon Jul 24 15:47:35 IRKT 2023 by ilyabarishnikov
\* Created Mon Apl 24 15:34:01 MSK 2023 by ilyabarishnikov
