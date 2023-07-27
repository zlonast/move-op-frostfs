-------------------------------- MODULE CRDT --------------------------------  

EXTENDS
  Naturals,
  Sequences,
  FiniteSets

CONSTANTS
  \* Time is type of time steps.
  Time,
  \* Node is type index node.
  Node,
  \* MetaMax is the maximum allowed meta data to be considered (starting from 1,
  \* including the MetaMax itself). This constraint was introduced to reduce
  \* the number of possible model states to be checked. It is recommended to
  \* keep this setting not too high.
  \* Example: 1
  MetaMax,
  \* RootNode is root Node of tree in file system.
  \* RootNode must be unique, which is why the model value.
  RootNode,
  \* TrashNode is trash Node of tree in file system.
  \* TrashNode must be unique, which is why the model value.
  \* We need TrashNode because delete operation is inefficient.
  TrashNode,
  \* Null is model value. We need it because emulate Maybe/Option data.
  Null,
  \* MaxSteps is the maximum allowed time steps to be considered (starting from 1).
  \* This constraint was introduced to reduce the number of possible model states to be checked. 
  \* It is recommended to keep this setting not too high.
  \* Example: 5
  MaxSteps,
  \* MaxWorkers is the maximum allowed workers to be exist (starting from 1).
  \* This constraint was introduced to reduce the number of possible model states to be checked. 
  \* It is recommended to keep this setting not too high.
  \* Example: 2
  MaxWorkers

VARIABLES
  \* logMove is a sequences of worker logs. It is represented by the
  \* mapping (function) with domain Workers to sequences LogMove.
  \* We need this to check the history of moves and redo some move if it was canceled earlier.
  logMove,
  \* treeSet is Set of TreeNode. TreeNode is tree edges with meta.
  \* treeSet is represent current tree in system. Tree of file system.
  treeSet,
  \* queue is sequences of worker moves. It is represented by the
  \* mapping (function) with domain Workers to sequences Move.
  \* We need nginx like thing.
  queue

\* vars is a tuple of all variables used in the specification. It is needed to
\* simplify fairness conditions definition.
vars == <<logMove, treeSet, queue>>

\* Nodes is set of all posible node.
Nodes == Node \union {RootNode} \union {TrashNode}

\* Workers is set of all posible workers.
Workers == 1..MaxWorkers

\* Meta is set of all posible meta.
Meta == 1..MetaMax

\* These assumptions are checked by the TLC model checker once at the start of
\* the model checking process. All the input data (declared constants) specified
\* in the "Model Overview" section must satisfy these constraints.
ASSUME
  /\ MetaMax    >= 1
  /\ MaxSteps   >= 1
  /\ MaxWorkers >= 1
  /\ MetaMax    \in Nat
  /\ MaxSteps   \in Nat
  /\ MaxWorkers \in Nat

(* -------------------------------- Types -------------------------------- *)

\* OldParentMeta is a set of records old parent and old meta
\* (with null because parent can don't exist).
OldParentMeta == [oldp : Nodes, oldm : Meta] \union {Null}

\* LogMove is a set of records we need to be in logs, when put move in it
\* like move's types and old parent and meta.
\* We need old values, bacause we want to undo moves.
LogMove == [log_time : Time, old_parent : OldParentMeta, new_parent : Nodes, log_meta : Meta, log_child : Nodes]

\* Move is a set of records what we need. Time for unique and order.
\* Parent and child for tree structure. Meta for other information.
\* Move is a general information we send to other workers.
Move == [move_time : Time, move_parent : Nodes, move_meta : Meta, move_child : Nodes]

\* TreeNode is a set of records represent the tree.
\* Parent and child for tree structure. Meta for other information.
TreeNode == [parent : Nodes, meta : Meta, child : Nodes]

(* -------------------------------- FUNCTIONS -------------------------------- *)

\* ancestor is function to check child is real child of parent.
RECURSIVE ancestor
ancestor[tree \in SUBSET(TreeNode), parent \in Nodes, child \in Nodes] ==
  \/ Cardinality({edge \in tree : edge.parent = parent /\ edge.child = child}) = 1
  \/ IF child = RootNode \/ Cardinality({edge \in tree : edge.child = child}) = 0
     THEN FALSE
     ELSE LET edgeChild == CHOOSE edge \in tree: edge.child = child
          IN ancestor[tree, parent, edgeChild.parent]

\* getParent is function to check child exist it tree if it exist return parent and meta.
getParent[tree \in SUBSET(TreeNode), child \in Nodes] ==
  IF Cardinality({edge \in tree: edge.child = child}) = 1
  THEN LET edge == CHOOSE edge \in tree: edge.child = child
       IN [oldp |-> edge.parent, oldm |-> edge.meta]
  ELSE Null

\* SetNodes is function to get nodes from tree.
SetNodes[tree \in SUBSET(TreeNode)] == {edge.child: edge \in tree}

\* timeSelf is function to calculate current time stemp.
timeSelf[self \in Workers] == Len(logMove[self]) * MaxWorkers + self

\* moveToLogMove is common function.
moveToLogMove[move \in Move, tree \in SUBSET(TreeNode)] ==
  [log_time   |-> move.move_time,
   old_parent |-> getParent[tree, move.move_child],
   new_parent |-> move.move_parent,
   log_meta   |-> move.move_meta,
   log_child  |-> move.move_child]

\* logMoveToMove is common function.
logMoveToMove[log \in LogMove] ==
  [move_time   |-> log.log_time, 
   move_parent |-> log.new_parent, 
   move_meta   |-> log.log_meta,
   move_child  |-> log.log_child]

\* findAllTreeNodes is function to find current subtree of node
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

\* HelpMove is helper function to create treeNode, move, log and change vars.
HelpMove(self, childCur, parentNew, metaNew, edgeChild, old) ==
  LET treeNode == [parent |-> parentNew, meta |-> metaNew, child |-> childCur]
      move == [move_time   |-> timeSelf[self],
               move_parent |-> treeNode.parent,
               move_meta   |-> treeNode.meta,
               move_child  |-> treeNode.child]
      log == [log_time   |-> move.move_time,
              old_parent |-> old,
              new_parent |-> move.move_parent,
              log_meta   |-> move.move_meta,
              log_child  |-> move.move_child]
  IN /\ treeSet' = [treeSet EXCEPT ![self] = (@ \ {edgeChild}) \union {treeNode}]
     /\ queue'   = [i \in Workers |-> IF i = self THEN queue[i] ELSE Append(queue[i], move)]
     /\ logMove' = [logMove EXCEPT ![self] = <<log>> \o @]

\* MoveLocal is a set of create, remove, and rehanging node.
\* Create edge with child = timeSelf[self] and pick parent in set of exist child or RootNode.
\* Remove subtree with root node in set of exist child and parent = TrashNode.
\* Move subtree with child in set of exist child and parent in set of exist child, but
\* the child is not an ancestor of the parent. 
MoveLocal(self) ==
  \E childCur \in (SetNodes[treeSet[self]] \union {timeSelf[self]}),
     parentNew \in (SetNodes[treeSet[self]] \union {RootNode} \union {TrashNode}),
     metaNew \in Meta:
  IF childCur = timeSelf[self]
  THEN /\ parentNew # TrashNode
       /\ HelpMove(self, childCur, parentNew, metaNew, Null, Null)
  ELSE LET edgeChild == CHOOSE edge \in treeSet[self]: edge.child = childCur
           old       == [oldp |-> edgeChild.parent, oldm |-> edgeChild.meta]
       IN /\ childCur # parentNew
          /\ edgeChild.parent # parentNew
          /\ (parentNew = TrashNode \/ ancestor[treeSet[self], childCur, parentNew] = FALSE)
          /\ HelpMove(self, childCur, parentNew, metaNew, edgeChild, old)

(* -------------------------------- Apply -------------------------------- *)

\* Undo last move in tree.
undoOp[log \in LogMove, tree \in SUBSET(TreeNode)] ==
  IF log.old_parent = Null
  THEN {edge \in tree: log.log_child # edge.child}
  ELSE LET treeNode == [parent |-> log.old_parent.oldp, meta |-> log.old_parent.oldm, child |-> log.log_child]
       IN {edge \in tree: log.log_child # edge.child} \union {treeNode}

\* Try to append move or do nothing.
doOp[move \in Move, tree \in SUBSET(TreeNode)] ==
  IF ancestor[tree, move.move_child, move.move_parent] \/ move.move_child = move.move_parent
  THEN tree
  ELSE LET treeNode == [parent |-> move.move_parent, meta |-> move.move_meta, child |-> move.move_child]
       IN {edge \in tree: move.move_child # edge.child} \union {treeNode}

\* Append move to logs and rebuild tree with current move.
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

\* If queue is not empty then do applyOp and change vars.
TryApply(self) ==
  /\ queue[self] # <<>>
  /\ LET move  == Head(queue[self])
         moves == Tail(queue[self])
         res   == applyOp[move, logMove[self], treeSet[self]]
     IN /\ queue'   = [queue   EXCEPT ![self] = moves]
        /\ logMove' = [logMove EXCEPT ![self] = res[1]]
        /\ treeSet' = [treeSet EXCEPT ![self] = res[2]]

(* -------------------------------- Init/Next/Spec -------------------------------- *)

\* Init is the initial predicate initializing values at the start of every
\* behaviour.
Init == /\ logMove = [self \in Workers |-> <<>>]
        /\ treeSet = [self \in Workers |-> {}]
        /\ queue   = [self \in Workers |-> <<>>]

\* Terminating is an action that allows infinite stuttering to prevent deadlock on
\* behaviour termination. We consider termination to be valid if at least do MaxSteps logs,
\* empty queue and all treeSet and logMove are the same.
Terminating ==
  /\ \A self \in Workers: Len(logMove[self]) >= MaxSteps /\ queue[self] = <<>>
  /\ \A i, j \in Workers: treeSet[i] = treeSet[j]
  /\ \A i, j \in Workers: logMove[i] = logMove[j]
  /\ UNCHANGED vars

\* Next is the next-state action describing the transition from the current state
\* to the next state of the behaviour.
Next ==
  \/ Terminating
  \/ \E self \in Workers: 
       \/ (Len(logMove[self]) < MaxSteps /\ (MoveLocal(self)))
       \/ TryApply(self)
        
\* Safety is a temporal formula that describes the whole set of allowed
\* behaviours. It specifies only what the system MAY do (i.e. the set of
\* possible allowed behaviours for the system). It asserts only what may
\* happen; any behaviour that violates it does so at some point and
\* nothing past that point makes difference.
\*
\* E.g. this safety formula (applied standalone) allows the behaviour to end
\* with an infinite set of stuttering steps (those steps that DO NOT change vars).
\*
\* To forbid such behaviours we must specify what the system MUST
\* do. It will be specified below with the help of fairness conditions in
\* the Fairness formula.
Safety == Init /\ [][Next]_vars

(* -------------------------------- Fairness -------------------------------- *)

\* Fairness is a temporal assumptions under which the model is working.
\* Usually it specifies different kind of assumptions for each/some
\* subactions of the Next's state action, but the only think that bothers
\* us is preventing infinite stuttering at those steps where some of Next's
\* subactions are enabled. Thus, the only thing that we require from the
\* system is to keep take the steps until it's impossible to take them.
\* That's exactly how the weak fairness condition works: if some action
\* remains continuously enabled, it must eventually happen.
Fairness == WF_vars(Next)

(* -------------------------------- Specification -------------------------------- *)

\* The complete specification of the protocol written as a temporal formula.
Spec == Safety /\ Fairness

(* -------------------------------- Liveness -------------------------------- *)

\* For every possible behaviour it's true that eventually (i.e. at least once
\* through the behaviour) move will sended and be accepted.
LivenessQueueToLogMove ==
  LET TimeConstant == 1..(MaxWorkers * MaxSteps)
  IN \A self \in Workers:
       \A moveTime \in TimeConstant:
         Cardinality({move \in ToSet(queue[self]): move.move_time = moveTime}) = 1
           ~> \E logTime \in TimeConstant:
             /\ Cardinality({log \in ToSet(logMove[self]): log.log_time = logTime}) = 1
             /\ moveTime = logTime

\* A liveness temporal formula asserts only what must happen (i.e. specifies
\* what the system MUST do). Any behaviour can NOT violate it at ANY point;
\* there's always the rest of the behaviour that can always make the liveness
\* formula true; if there's no such behaviour than the liveness formula is
\* violated. The liveness formula is supposed to be checked as a property
\* by the TLC model checker.
Liveness == LivenessQueueToLogMove

(* -------------------------------- ModelConstraints -------------------------------- *)

\* MaxViewConstraint is a state predicate restricting the number of possible
\* behaviour states. It is needed to reduce model checking time and prevent
\* the model graph size explosion. This formulae must be specified at the
\* "State constraint" section of the "Additional Spec Options" section inside
\* the model overview.
ModelConstraints == \A self \in Workers: (Len(logMove[self]) < MaxSteps) /\ (Len(queue[self]) <= MaxWorkers)

(* -------------------------------- Invariants -------------------------------- *)

\* Model invariant is a state predicate (statement) that must be true for
\* every step of every reachable behaviour. Model invariant is supposed to
\* be checked as an Invariant by the TLC Model Checker.

\* TypeOK is a type-correctness invariant. It states that all elements of
\* specification variables must have the proper type throughout the behaviour.
TypeOK == /\ logMove \in [Workers -> Seq(LogMove)]
          /\ treeSet \in [Workers -> SUBSET(TreeNode)]
          /\ queue   \in [Workers -> Seq(Move)]

\* InvOneParent states that there can be only one parent exist to each child.
InvOneParent == \A self \in Workers:
             \A child \in {edge.child: edge \in treeSet[self]}: 
             Cardinality({edge \in treeSet[self]: child = edge.child}) = 1

\* InvTwoBeginnings states that there can be only 2 general nodes in tree.
InvTwoBeginnings ==
  \A self \in Workers:
  LET rootTree  == findAllTreeNodes[treeSet[self], RootNode]
      trashTree == findAllTreeNodes[treeSet[self], TrashNode]
  IN (rootTree \union trashTree) = treeSet[self]

\* We could prove that the trees don’t get tangled together.
InvTwoTangledTree ==
  \A self \in Workers:
  LET rootTree  == findAllTreeNodes[treeSet[self], RootNode]
      trashTree == findAllTreeNodes[treeSet[self], TrashNode]
  IN (rootTree \intersect trashTree) = {}

\* InvEmprtyLogAndTree states that logMove can be empty then and only then treeSet is empty.
InvEmprtyLogAndTree ==
  \A self \in Workers:
  logMove[self] = <<>> <=> treeSet[self] = {}

\* The graph contains no cycles.
InvAcyclic ==
  \A self \in Workers:
  \A node \in SetNodes[treeSet[self]]: 
  ancestor[treeSet[self], node, node] = FALSE

\* No two operations with the same timestamp.
InvTwoMoveTime ==
  \A self \in Workers:
  \A log1 \in logMove[self], log2 \in logMove[self]:
  log1 = log2 \/ log1.log_time # log2.log.time

\* ModelConstSizeLogMove states that there logMove have size between 0 to MaxWorkers * MaxSteps.
ModelConstSizeLogMove == \A self \in Workers:
  LET size == Len(logMove[self]) 
  IN 0 <= size /\ size <= MaxWorkers * MaxSteps

\* ModelConstSizeLogMove states that there treeSet have size between 0 to MaxWorkers * MaxSteps.
ModelConstSizeTreeSet == \A self \in Workers:
  LET size == Cardinality(treeSet[self])
  IN 0 <= size /\ size <= MaxWorkers * MaxSteps

\* ModelConstSizeLogMove states that there queue have size between 0 to (MaxWorkers - 1) * MaxSteps.
ModelConstSizeQueue == \A self \in Workers:
  LET size == Len(queue[self])
  IN 0 <= size /\ size <= (MaxWorkers - 1) * MaxSteps

\* This theorem asserts the truth of the temporal formula whose meaning is that
\* the state predicates TypeOK, InvOneParent, InvTwoBeginnings and exts are
\* the invariants of the specification Spec. This theorem is not supposed to be
\* checked by the TLC model checker, it's here for the reader's understanding of
\* the purpose of TypeOK, InvTwoBlocksAccepted and InvFaultNodesCount.
THEOREM Spec => [](TypeOK /\ InvOneParent /\ InvTwoBeginnings /\ InvTwoTangledTree /\ InvEmprtyLogAndTree /\ InvAcyclic /\ InvTwoMoveTime
                   /\ ModelConstSizeLogMove /\ ModelConstSizeTreeSet /\ ModelConstSizeQueue)

=============================================================================
\* Modification History
\* Last modified Thu Jul 27 22:50:05 IRKT 2023 by ilyabarishnikov
\* Created Mon Apl 24 15:34:01 MSK 2023 by ilyabarishnikov
