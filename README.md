# PnVRocqLib

A Coq library written by members of PnV Discord Server.

Currently, this library is standalone.

## 1. Quick Start

```
git clone https://github.com/PnVDiscord/PnVRocqLib.git
cd PnVRocqLib
eval `opam env`
coq_makefile -f _CoqProject -o Makefile
make -j4 -k
```

### `coqc -v`

```
The Coq Proof Assistant, version 8.20.0
compiled with OCaml 5.2.0
```

## 2. Contents

Our main results are:

- [x] The Kleene fixed-point theorem. (`Theorem lfp_returns_the_least_fixed_point` in [`ClassicalDomainTheory.v`](theories/Math/ClassicalDomainTheory.v))

- [x] The weak completeness of propositional logic. (`Corollary weak_completeness` in [`PropositionalLogic.v`](theories/Logic/PropositionalLogic.v))

- [x] The soundness, completeness, and compactness theorems of propositional logic. (`Theorem the_propositional_soundness_theorem`, `Theorem the_propositional_completeness_theorem`, and `Corollary the_propositional_compactness_theorem` in [`ClassicalPropositionalLogic.v`](theories/Logic/ClassicalPropositionalLogic.v))

- [x] The soundness and countable completeness theorems of first-order logic. (`Theorem HilbertCalculus_sound` and `Theorem HilbertCalculus_countable_complete` in [`ClassicalFol.v`](theories/Logic/ClassicalFol.v))

### Control

- `Category.v` : Basic theory on category

- `Monad.v` : Basic definitions about monad

### Data

- `Aczel.v` : Aczel's type theoretic interpretation of set theory.

- `Graph.v` : Basic graph theory.

- `ITree.v` : Basic Definitions on interaction tree.

- `Vector.v` : Replaces `Stdlib.Vectors.VectorDef.t`.

### Index

- `Index.v` : Accumulates all source files and check their consistency.

### Logic

- `BasicFol.v` : Basic definitions of First-Order Logic.

- `BasicFol2.v` : Extra definitions of First-Order Logic.

- `ClassicalFol.v` : The meta-theory on Classical First-Order Logic--such as Soundness Theorem and Completeness Theorem.

- `ClassicalPropositionalLogic.v` : The Soundness, Completeness, and Compactness Theorem for PropositionalLogic.

- `ExtraFol.v` : Extra def/thm about First-Order Logic.

- `HilbertFol.v` : Basic facts about Hilbert calculus for First-Order Logic.

- `HilbertFol2.v` : Advanced facts about Hilbert calculus for First-Order Logic.

- `MuRec.v` : Basic facts about μ-recursive functions.

- `PrimRec.v` : Basic facts about primitive recursive functions.

- `PropositionalLogic.v` : Contructive meta-theory on the Propositional Logic, Weak Completeness Theorem for PropoistionalLogic.

### Math

- `BooleanAlgebra.v` : Basic theory on Boolean algebras.

- `ClassicalDomainTheory.v` : Classical domain theory.

- `DomainTheory.v` : Constructive domain theory.

- `OrderTheory.v` : Basic order theory.

- `Ordinal.v` : Theory on ordinal numbers.

- `ThN.v` : Basic facts about the natural numbers.

### Prelude

- `AC.v` : Facts about `CIC` + Axiom of Choice.

- `ClassicalFacts.v` : Facts about `CIC + (classic : forall P, P \/ ~ P)`.

- `ConstructiveFacts.v` : Facts about CIC.

- `Notations.v` : Reserves all notations to avoid the conflict.

- `SfLib.v` : The copy of `snu-sf/sflib.v`.

- `Prelude.v` : The prelude code.

### System

- `BasicITreeTh.v` : A basic theory on interaction trees.

- `Regex.v` : A theory on regular expression.

## 3. References

1. [sflib](https://github.com/snu-sf/sflib)

2. [stdpp](https://plv.mpi-sws.org/coqdoc/stdpp)

3. [A note written by Jayadev Misra](https://www.cs.utexas.edu/users/misra/Notes.dir/KnasterTarski.pdf)

4. [Constructive Completeness Proofs and Delimited Control](https://theses.hal.science/pastel-00530424/)

5. [Murec_Extraction](https://github.com/DmxLarchey/Murec_Extraction)

6. [CoqGym/goedel](https://github.com/princeton-vl/CoqGym/tree/master/coq_projects/goedel)

7. [formalmetatheory-stoughton](https://github.com/ernius/formalmetatheory-stoughton)

8. [Constructive Analysis of First-Order Completeness](https://github.com/uds-psl/fol-completeness-theorems/tree/master)

9. [snu-sf/Ordinal](https://github.com/snu-sf/Ordinal)
