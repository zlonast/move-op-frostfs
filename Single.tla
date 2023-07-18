------------------------------- MODULE Single -------------------------------
EXTENDS TLC, Naturals, Sequences, Integers, FiniteSets

CONSTANTS Time, Nodes, Meta, Root, Null

Move == Time \X Nodes \X Meta \X Nodes

\* (parent, meta, child) в root положить module value вместо parent и child
TreeNode == [parent : Nodes, meta : Meta, child : Nodes]

\* TODO мб сделать assume на то что в любой момент времени существуе только одна пара <<parent, _, child>> ?

VARIABLES treeSet \* set of edges (parent, meta, child).
  
 
vars == <<treeSet>>

TypeOK == treeSet \subseteq TreeNode

Init == treeSet = {}

WithNull(smth) == smth \union {Null}

\*  (’n × ’m × ’n) set ⇒ ’n ⇒ ’n ⇒ bool
RECURSIVE ancestor
ancestor[tree \in SUBSET(TreeNode), parent \in Nodes, child \in Nodes] ==
  \/ Cardinality({edge \in tree : edge.parent = parent /\ edge.child = child}) # 0
  \/ \E edge2 \in tree: {edge1 \in tree: ancestor[tree, parent, edge2.parent] /\ edge1.child = edge2.child}

(*
\* переписать на рекорды???
\* сделать рандомную последовательность и из неё брать таймсстепы
\* [type : "noExist", view : <<{}, {}>>] \* поменять на null \* model value
\* мы же никак не решаем баги со временем и дублированием?
*)

(*
\* сделать сингл версию (генерация всех операций на одной машине)
\* спросить про оптимизацию choose условий
*)

findNode[tree \in SUBSET(TreeNode), node \in Nodes] == 
  Cardinality({<<p, m, c>> \in tree: p = node \/ c = node}) # 0

\* вначале удаляем <<_, _, node>> а затем ищем <<node, _, child>> и делаем рекурсию от findAllTreeNodes(newTree, child)
\* мап на <<node, _, child>> и в findAllTreeNodes(tree, child) и в конце \union всех
RECURSIVE findAllTreeNodes
findAllTreeNodes[tree \in SUBSET(TreeNode), node \in Nodes] ==
  LET pEdge  == CHOOSE edge \in tree: edge.child = node
      filter == {edge \in tree: edge.parent = node}
      maps   == UNION {findAllTreeNodes[tree, edge.child] : edge \in filter}
  IN maps \union filter \union {pEdge}

AppendE ==
  LET node == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = FALSE
  IN IF treeSet = {}
     THEN treeSet' = {[parent |-> 0, meta |-> 0, child |-> node]}
     ELSE LET parent == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = TRUE
          IN /\ treeSet' = treeSet \union {[parent |-> parent, meta |-> 0, child |-> node]}
             /\ UNCHANGED <<>>
  
Remove ==
  IF treeSet = {}
  THEN UNCHANGED <<treeSet>>
  ELSE LET node == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = TRUE
           treeNodes == findAllTreeNodes[treeSet, node]
       IN /\ treeSet' = treeSet \intersect treeNodes
          /\ UNCHANGED <<>>

Move ==
  IF treeSet = {}
  THEN UNCHANGED <<treeSet>>
  ELSE \E nodeChild \in 1..MaxNodes, nodeParent \in 1..MaxNodes: 
         /\ nodeChild # nodeParent
         /\ findNode[treeSet, nodeChild] = TRUE
         /\ findNode[treeSet, nodeParent] = TRUE
         /\ ancestor[treeSet, nodeChild, nodeParent] = FALSE
         /\ LET treeNode == CHOOSE edge \in treeSet: edge.child = nodeChild 
            IN /\ treeSet' = (treeSet \intersect {treeNode}) \union {[parent |-> nodeParent, meta |-> treeNode.meta, child |-> nodeChild]}
               /\ UNCHANGED <<>>

NextLocal == AppendE \/ Remove \/ Move

SendMove(move) == {}

(*
local  -> send -> apply
single ->     multy
*)

Next == LET move == NextLocal IN SendMove(move)

\* инвариант что дерево в любой момент времени коректное
\* инвариант в конце концов они все придут к одному состоянию
\* инвариант что родитель всегда один

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Tue Jul 04 16:42:40 MSK 2023 by ilyabarishnikov
\* Created Mon Jul 03 13:31:03 MSK 2023 by ilyabarishnikov
