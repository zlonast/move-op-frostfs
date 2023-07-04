------------------------------- MODULE Single -------------------------------
EXTENDS TLC, Naturals, Sequences, Integers, FiniteSets

CONSTANTS Time, Nodes, Meta

Move == Time \X Nodes \X Meta \X Nodes

\* (parent, meta, child) в root положить module value вместо parent и child
TreeNode == Nodes \X Meta \X Nodes

\* TODO мб сделать assume на то что в любой момент времени существуе только одна пара <<parent, _, child>> ?

ROOT <- [model value]
NULL <- [model value]

VARIABLES treeSet \* set of edges (parent, meta, child).
  
 
vars == <<treeSet>>

TypeOK == treeSet \subseteq TreeNode

Init == treeSet = {}

\*  (’n × ’m × ’n) set ⇒ ’n ⇒ ’n ⇒ bool
RECURSIVE ancestor
ancestor == 
  [tree \in SUBSET(TreeNode), parent \in Nodes, child  \in Nodes |-> 
    \/ Cardinality({<<p1, m1, c1>> \in tree : p1 = parent /\ c1 = child}) # 0
    \/ \E <<p2, m2, c2>> \in tree: {<<p1, m1, c1>> \in tree: ancestor[tree, parent, p2] /\ c1 = c2}
  ]

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

findNode ==
  [tree \in SUBSET(TreeNode), node \in Nodes |-> 
   Cardinality({<<p, m, c>> \in tree: p = node \/ c = node}) # 0
  ]

\* вначале удаляем <<_, _, node>> а затем ищем <<node, _, child>> и делаем рекурсию от findAllTreeNodes(newTree, child)
\* мап на <<node, _, child>> и в findAllTreeNodes(tree, child) и в конце \union всех
RECURSIVE findAllTreeNodes
findAllTreeNodes == 
  [tree \in SUBSET(TreeNode), node \in Nodes |-> 
     LET pEdge  == CHOOSE <<p, m, c>> \in tree: c = node
         filter == {<<p, m, child>> \in tree: p = node}
         maps   == UNION {findAllTreeNodes[tree, child] : <<p, m, child>> \in filter}
     IN maps \union filter \union {pEdge}]

AppendE ==
  LET node == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = FALSE
  IN IF treeSet = {}
     THEN treeSet' = {<<0, 0, node>>} \* TODO мне не нравятся нули, хочу модел валуе
     \* написать тут через choose и рандом наверное выбор следующего такой parent или child уже должен существовать в дереве
     ELSE LET parent == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = TRUE
          IN /\ treeSet' = treeSet \union {<<parent, 0, node>>}
             /\ UNCHANGED <<>>
  
Remove ==
  IF treeSet = {}
  THEN UNCHANGED <<treeSet>>
  \* найти такого node у которого нет child или взять parent, но убрать сразу все поддерево
  ELSE LET node == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = TRUE
           \* операция которая удаляет все поддерево рекурсивно
           treeNodes == findAllTreeNodes[treeSet, node]
       IN /\ treeSet' = treeSet \intersect treeNodes
          /\ UNCHANGED <<>>

findTreeNode == 
  [tree \in SUBSET(TreeNode), child \in Nodes |-> 
    {<<p, m, c>> \in tree: c = child}
  ]

Move ==
  IF treeSet = {}
  THEN UNCHANGED <<treeSet>>
  ELSE LET nodeChild == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = TRUE
           nodeNewParent == CHOOSE n \in 1..MaxNodes : findNode[treeSet, n] = TRUE /\ ancestor[treeSet, nodeChild, n] = FALSE
           treeNode == findTreeNode[treeSet, nodeChild]
       \* нужно переместить старое ребро между child и его parent к new parent <<p1, m,c>> -> <<np, m, c>>
       IN /\ treeSet' = (treeSet \intersect treeNode) \union {<<nodeNewParent, treeNode[2], nodeChild>>}
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
\* Last modified Tue Jul 04 16:39:15 MSK 2023 by ilyabarishnikov
\* Created Mon Jul 03 13:31:03 MSK 2023 by ilyabarishnikov
