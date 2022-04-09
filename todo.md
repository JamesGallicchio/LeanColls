# TODO

- Finish correctness proofs for RTQueue
- Implement
  - OrdMap
  - RBTree
  - HashMap
---
- Read about thread safety in immutable beans paper
- Skim Lorenzen's thesis
- Read about Isabelle Containers


## Done

### 14 Apr 2022
- Implemented improved Array/ArrayBuffer (no more Option boxes!)

### 5 Apr 2022
- Bashed head against RealTimeQueue proof issues
  - (Should be improved in a few months)[https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Cannot.20rewrite.20term.20being.20cased.20on]
- Figured out FFI for fixed length arrays


### 15 Mar 2022
- Finished (non-augmented) finger tree implementation with proofs
- Proved correctness for LazyBatchQueue
- Added collection classes
- Implemented Range
- Worked on static-size arrays

### 1 Mar 2022
- Read about Haskell collections
- Implemented finger trees (mostly)
- Fold is specialized ForIn, maybe worth keeping separate?

### 22 Feb 2022
- Looked into F# collections, Agda collections, Coq collections, Isabelle collections
- Implemented real-time queues, which completes the first set of collections I wanted to try implementing.

### 15 Feb 2022
- Wrote some stuff about finite streams
- Implemented LBQueue
  - Found minor bugs in my LazyList impl while proving correctness
  - Need to prove correctness of deq
- Wrote tests for queues
- Already hit 2 bugs and counting :D
- Skimmed Isabelle Collections Framework paper

### 8 Feb 2022
- Implemented BQueue
- Fleshed out Fold