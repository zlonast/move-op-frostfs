# A highly-available move operation for replicated trees

A port of https://martin.kleppmann.com/papers/move-op.pdf to TLA+.

Paper authors: Martin Kleppmann, Dominic P. Mulligan, Victor B. F. Gomes, and Alastair R. Beresford.

**Abstract**—Replicated tree data structures are a fundamental building block of distributed filesystems, such as Google Drive and
Dropbox, and collaborative applications with a JSON or XML data model. These systems need to support a move operation that allows
a subtree to be moved to a new location within the tree. However, such a move operation is difficult to implement correctly if different
replicas can concurrently perform arbitrary move operations, and we demonstrate bugs in Google Drive and Dropbox that arise with
concurrent moves. In this paper we present a CRDT algorithm that handles arbitrary concurrent modifications on trees, while ensuring
that the tree structure remains valid (in particular, no cycles are introduced), and guaranteeing that all replicas converge towards the
same consistent state. Our algorithm requires no synchronous coordination between replicas, making it highly available in the face of
network partitions. We formally prove the correctness of our algorithm using the Isabelle/HOL proof assistant, and evaluate the
performance of our formally verified implementation in a geo-replicated setting.

**Index** Terms—Conflict-free Replicated Data Types (CRDTs), formal verification, distributed filesystems, distributed collaboration

## CRDT formal models

This section contains a set of CRDT's formal specifications written in
[TLA⁺](https://lamport.azurewebsites.net/tla/tla.html) language. The models
describe the core algorithm logic represented in a high-level way and can be used
to illustrate some basic CRDT concepts and to validate the algorithm in terms of
liveness and fairness. It should be noted that presented models do not precisely
follow the CRDT implementation presented in the repository and may omit some
implementation details in favor of the specification simplicity and the
fundamental philosophy of the TLA⁺. However, the presented models directly
reflect some liveness problems CRDT has; the models can and are aimed to be
used for the CRDT liveness evaluation and further algorithm improvements.

Any contributions, questions and discussions on the presented models are highly
appreciated.

## How to run/check the TLA⁺ specification

### Prerequirements

1. Download and install the TLA⁺ Toolbox following the
   [official guide](http://lamport.azurewebsites.net/tla/toolbox.html).
2. Read the brief introduction to the TLA⁺ language and TLC Model Checker at the
   [official site](http://lamport.azurewebsites.net/tla/high-level-view.html).
3. Download and take a look at the
   [TLA⁺ cheat sheet](https://lamport.azurewebsites.net/tla/summary-standalone.pdf).
4. For a proficient learning watch the
   [TLA⁺ Video Course](https://lamport.azurewebsites.net/video/videos.html) and
   read the [Specifying Systems book](http://lamport.azurewebsites.net/tla/book.html?back-link=tools.html#documentation).

### Running the TLC model checker

1. Clone the [repository](https://github.com/nspcc-dev/dbft.git).
2. Open the TLA⁺ Toolbox, open new specification and provide path to the desired
   `*.tla` file that contains the specification description.
3. Create the model named `Model_1` in the TLA⁺ Toolbox.
4. Copy the corresponding `*___Model_1.launch` file to the `*.toolbox`
   folder. Reload/refresh the model in the TLA⁺ Toolbox.
5. Open the `Model Overview` window in the TLA⁺ Toolbox  and check that behaviour
   specification, declared constants, invariants and properties of the model are
   filled in with some values.
6. Press `Run TLC on the model` button to start the model checking process and
   explore the progress in the `Model Checkng Results` window.
