-------------------------------- MODULE Move --------------------------------  
EXTENDS TLC, Naturals, Sequences, Integers, FiniteSets

CONSTANTS Time, Nodes, Meta, Root, Null, MaxNodes, MaxSteps

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

WithNull(smth) == smth \union {Null}

OldParentStates == [oldp : Nodes, oldm : Meta] \union {Null}

LogMove == [log_time : Time, old_parent : OldParentStates, new_parent : Nodes, log_meta : Meta, log_child : Nodes]

Move == [move_time : Time, move_parent : Nodes, move_meta : Meta, move_child : Nodes]

TreeNode == [parent : Nodes, meta : Meta, child : Nodes]

Workers == {1, 2, 3, 4}

TypeOK == /\ logMove   \in [Workers -> SUBSET(LogMove)]
          /\ treeSet   \in [Workers -> SUBSET(TreeNode)]
          /\ queue     \in [Workers -> Seq(Move)]
          /\ localTime \in [Workers -> Time]
          /\ Workers \in SUBSET(Time) \* я уже хз

Init == /\ logMove   = [self \in Workers |-> {}]
        /\ treeSet   = [self \in Workers |-> {}]
        /\ queue     = [self \in Workers |-> <<>>]
        /\ localTime = [self \in Workers |-> 0]

(* -------------------------FUNCTIONS------------------------------------ *)

findNode[tree \in SUBSET(TreeNode), node \in Nodes] == 
  Cardinality({edge \in tree: edge.parent = node \/ edge.child = node}) # 0

RECURSIVE findAllTreeNodes
findAllTreeNodes[tree \in SUBSET(TreeNode), node \in Nodes] ==
  LET pEdge  == CHOOSE edge \in tree: edge.child = node
      filter == {edge \in tree: edge.parent = node}
      maps   == UNION {findAllTreeNodes[tree, edge.child] : edge \in filter}
  IN maps \union filter \union {pEdge}

\*  (’n × ’m × ’n) set ⇒ ’n ⇒ ’n ⇒ bool
RECURSIVE ancestor
ancestor[tree \in SUBSET(TreeNode), parent \in Nodes, child \in Nodes] ==
  \/ Cardinality({edge \in tree : edge.parent = parent /\ edge.child = child}) # 0
  \/ \E edge2 \in tree: {edge1 \in tree: ancestor[tree, parent, edge2.parent] /\ edge1.child = edge2.child}

\* 〈 (’n × ’m × ’n) set ⇒ ’n ⇒ (’n × ’m) option 
getParent[tree \in SUBSET(TreeNode), child \in Nodes] ==
  IF findNode[tree, child] = TRUE 
  THEN LET treeNode == CHOOSE edge \in treeSet: edge.child = child
       IN {<<treeNode.parent, treeNode.meta>>}
  ELSE Null

\* (’t, ’n, ’m) log_op ⇒ (’t, ’n, ’m) operation
logMoveToMove[log \in LogMove] ==
  [move_time : log.log_time, move_parent : log.new_parent, move_meta : log.log_meta, move_child : log.log_child]

SendMove(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ queue' = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
  /\ localTime' = [localTime EXCEPT ![self] = localTime[self] + 1]
  /\ UNCHANGED <<logMove, treeSet>>

(* -----------------------SINGLE------------------------------------------ *)

AppendE(self) ==
  /\ self \in Workers
  /\ \E node \in 1..MaxNodes : 
     /\ findNode[treeSet[self], node] = FALSE
     /\ IF treeSet[self] = {}
        THEN LET treeNode == [parent |-> 0, meta |-> 0, child |-> node]
                 move     == [move_time   |-> localTime[self] * 10 + self,
                              move_parent |-> treeNode.parent,
                              move_meta   |-> treeNode.meta,
                              move_child  |-> treeNode.child]
             IN /\ treeSet' = [treeSet EXCEPT ![self] = {treeNode}]
                /\ queue' = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
                /\ localTime' = [localTime EXCEPT ![self] = localTime[self] + 1]
        ELSE LET parent   == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = TRUE \* мб стоит спросить
                 treeNode == [parent |-> parent, meta |-> 0, child |-> node]
                 move     == [move_time   |-> localTime[self] * 10 + self,
                              move_parent |-> treeNode.parent,
                              move_meta   |-> treeNode.meta,
                              move_child  |-> treeNode.child]
             IN /\ treeSet' = [treeSet EXCEPT ![self] = treeSet[self] \union {treeNode}]
                /\ queue' = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
                /\ localTime' = [localTime EXCEPT ![self] = localTime[self] + 1]
  /\ UNCHANGED <<logMove>>

RemoveE(self) ==
  /\ self \in Workers
  /\ IF treeSet[self] = {}
     THEN UNCHANGED <<treeSet>>
     ELSE LET node      == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = TRUE
              treeNodes == findAllTreeNodes[treeSet[self], node]
              move      == [move_time   |-> localTime[self] * 10 + self,
                            move_parent |-> 0, \* TODO надо добавить треш_ноду?
                            move_meta   |-> node.meta,
                            move_child  |-> node.child]
          IN /\ treeSet' = [treeSet EXCEPT ![self] = treeSet[self] \intersect treeNodes]
             /\ queue' = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
             /\ localTime' = [localTime EXCEPT ![self] = localTime[self] + 1]
  /\ UNCHANGED <<logMove>>

MoveE(self) ==
  /\ self \in Workers
  /\ IF treeSet = {}
     THEN UNCHANGED <<treeSet>>
     ELSE \E nodeChild \in 1..MaxNodes, nodeParent \in 1..MaxNodes: 
          /\ nodeChild # nodeParent
          /\ findNode[treeSet, nodeChild] = TRUE
          /\ findNode[treeSet, nodeParent] = TRUE
          /\ ancestor[treeSet, nodeChild, nodeParent] = FALSE
          /\ LET childNode == CHOOSE edge \in treeSet: edge.child = nodeChild
                 treeNode  == [parent |-> nodeParent, meta |-> childNode.meta, child |-> nodeChild]
                 move      == [move_time   |-> localTime[self] * 10 + self,
                               move_parent |-> treeNode.parent,
                               move_meta   |-> treeNode.meta,
                               move_child  |-> treeNode.child]
             IN /\ treeSet' = [treeSet EXCEPT ![self] = (treeSet[self] \intersect {childNode}) \union {treeNode}]
                /\ queue' = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
                /\ localTime' = [localTime EXCEPT ![self] = localTime[self] + 1]
  /\ UNCHANGED <<logMove>>

(* -----------------------Apply------------------------------------------ *)

\* (’t, ’n, ’m) log_op × (’n × ’m × ’n) set ⇒ (’n × ’m × ’n) set
UndoOp(self, log) ==
  /\ self \in Workers
  /\ log \in LogMove
  /\ \/ /\ log.old_parent = Null
        /\ treeSet' = {edge \in treeSet[self]: log.log_child /= edge.child}
     \/ /\ log.old_parent # Null
        /\ LET treeNode == [parent |-> log.old_parent.oldp, meta |-> log.old_parent.oldm, child |-> log.log_child]
           IN treeSet' = [treeSet EXCEPT ![self] = {edge \in treeSet[self]: log.log_child /= edge.child} \union {treeNode}]
  /\ UNCHANGED <<logMove, queue, localTime>>

\* 〈 (’t, ’n, ’m) operation × (’n × ’m × ’n) set ⇒ (’t, ’n, ’m) log_op × (’n × ’m × ’n) set 〉
DoOp(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ IF ancestor[treeSet, move.move_child, move.move_parent] \/ move.move_child = move.move_parent 
     THEN treeSet' = treeSet
     ELSE LET treeNode == [parent |-> move.move_parent, meta |-> move.move_meta, child |-> move.move_child]
          IN treeSet' = [treeSet EXCEPT ![self] = {edge \in treeSet[self]: edge.child /= move.move_child} \union {treeNode}]
  /\ [move_time   : move.move_time, 
      move_parent : getParent[treeSet, move.move_child], 
      move_meta   : move.move_meta, 
      move_child  : move.move_child]
  /\ UNCHANGED <<logMove, queue, localTime>>

\* (’t, ’n, ’m) log_op ⇒ (’t, ’n, ’m) state ⇒ (’t, ’n, ’m) state
RedoOp(self, log) ==
  /\ self \in Workers
  /\ log \in LogMove
  /\ logMove' = [logMove EXCEPT ![self] = DoOp (self, logMoveToMove[log]) \o logMove[self]]
  /\ UNCHANGED <<treeSet, queue, localTime>>

\* (’t::{linorder}, ’n, ’m) operation ⇒ (’t, ’n, ’m) state ⇒ (’t, ’n, ’m) state 〉
RECURSIVE ApplyOp(_, _)
ApplyOp(self, move) ==
  /\ self \in Workers
  /\ move \in Move
  /\ IF logMove = {}
     THEN LET op == DoOp(self, move)
          IN /\ logMove' = [logMove EXCEPT ![self] = op \o logMove]
             /\ UNCHANGED <<logMove, queue, localTime>>
     ELSE LET logop == Head(logMove)
              ops   == Tail(logMove)
          IN IF move.move_time < logop.log_time
             THEN /\ UndoOp(self, logop)  \* не меняет логмув, только дерево
                  /\ logMove' = [logMove EXCEPT ![self] = ops] \*
                  /\ ApplyOp(self, move)  \* меняет логмув и дерево
                  /\ RedoOp(self, logop)  \* меняет логмув и дерево
             ELSE LET op == DoOp (self, move) \* не меняет логмув, только дерево
                  IN /\ logMove' = [logMove EXCEPT ![self] = op \o logop \o ops]
                     /\ UNCHANGED <<treeSet, queue, localTime>> \* не понятно, что это значит, мб моделька попросить убрать

TryApply(self) ==
  /\ queue[self] # <<>>
  /\ LET move  == Head(queue[self])
         moves == Tail(queue[self])
     IN /\ queue' = [queue EXCEPT ![self] = moves]
        \* /\ ApplyOp(self, move)
        /\ UNCHANGED <<logMove, treeSet, localTime>>

(* -------------------------------------------------------------------------- *)

BoundedData(Data, n) == { s \in Data : s <= n }

Next == \/ (\E self \in Workers: localTime[self] < MaxSteps /\ (AppendE(self) \/ RemoveE(self) \/ MoveE(self)))
        \* \/ (\E self \in Workers: TryApply(self))

FullStop == \A self \in Workers: localTime[self] = MaxSteps /\ queue[self] = <<>>

IsFull == 
  LET RECURSIVE Helper(_, _)
      Helper(tree, S) == 
      IF tree = {} THEN S 
      ELSE LET edge == CHOOSE edge \in tree : TRUE
           IN Helper(tree \ {edge}, S \union {edge.parent, edge.child})
  IN Cardinality(Helper(treeSet, {})) = MaxNodes + 1 \* еще и root в виде 0

InvariantTree == IF FullStop THEN FALSE ELSE TRUE
\* инвариант что дерево в любой момент времени коректное
\* инвариант в конце концов они все придут к одному состоянию
\* инвариант что родитель всегда один

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Tue Jul 18 21:40:59 IRKT 2023 by ilyabarishnikov
\* Created Mon Apl 24 15:34:01 MSK 2023 by ilyabarishnikov
