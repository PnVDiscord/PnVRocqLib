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

### coqc -v

```
The Coq Proof Assistant, version 8.18.0
```

## 2. Contents

Our main results are:

- [x] The Kleene fixed-point theorem. (`Theorem lfp_returns_the_least_fixed_point` in [`ClassicalDomainTheory.v`](theories/Math/ClassicalDomainTheory.v))

- [x] The weak completeness of propositional logic. (`Corollary weak_completeness` in [`PropositionalLogic.v`](theories/Logic/PropositionalLogic.v))

- [x] The soundness, completeness, and compactness theorems of propositional logic. (`Theorem the_propositional_soundness_theorem`, `Theorem the_propositional_completeness_theorem`, and `Corollary the_propositional_compactness_theorem` in [`ClassicalPropositionalLogic.v`](theories/Logic/ClassicalPropositionalLogic.v))

- [x] The soundness and completeness theorems of first-order logic. (`Theorem HilbertCalculus_sound` and `Theorem HilbertCalculus_complete` in [`ClassicalFol.v`](theories/Logic/ClassicalFol.v))

### Data

- `Aczel.v` : Aczel's Type Theoretic Interpretation of Set Theory.

- `Graph.v` : Basic Graph Theory.

- `Vector.v` : Replaces `Coq.Vectors.VectorDef.t`.

### Logic

- `BasicFol.v` : Basic definitions of First-Order Logic.

- `BasicFol2.v` : Extra definitions of First-Order Logic.

- `ClassicalFol.v` : Meta-theories on Classical First-Order Logic--such as Soundness Theorem and Completeness Theorem.

- `ClassicalPropositionalLogic.v` : The Soundness, Completeness, and Compactness Theorem for PropositionalLogic.

- `HilbertFol.v` : Basic facts on Hilbert calculus for First-Order Logic.

- `HilbertFol2.v` : Advanced facts on Hilbert calculus for First-Order Logic.

- `MuRec.v` : Basic facts on μ-recursive functions.

- `PrimRec.v` : Basic facts on primitive recursive functions.

- `PropositionalLogic.v` : Contructive meta-theory on the Propositional Logic, Weak Completeness Theorem for PropoistionalLogic.

### Index

- `Index.v` : Accumulates all source files and check their consistency.

### Math

- `BooleanAlgebra.v` : Basic theory on Boolean Algebras.

- `ClassicalDomainTheory.v` : Classical domain theory.

- `DomainTheory.v` : Constructive domain theory.

- `OrderTheory.v` : Basic order theory.

- `Ordinal.v` : Theory on ordinal numbers.

- `ThN.v` : Basic facts on the natural numbers.

### Prelude

- `AC.v` : Facts on `CIC` + Axiom of Choice.

- `Classical.v` : Facts on `CIC` + `classic : forall P, P \/ ~ P`.

- `ConstructiveFacts.v` : Facts on CIC.

- `Notations.v` : Reserves all notations to avoid the conflict.

- `SfLib.v` : The copy of `snu-sf/sflib.v`.

- `Prelude.v` : The prelude code.

## 3. References

1. [sflib](https://github.com/snu-sf/sflib)

2. [stdpp](https://plv.mpi-sws.org/coqdoc/stdpp)

3. [A note written by Jayadev Misra](https://www.cs.utexas.edu/users/misra/Notes.dir/KnasterTarski.pdf)

4. [Constructive Completeness Proofs and Delimited Control](https://theses.hal.science/pastel-00530424/)

5. [Murec_Extraction](https://github.com/DmxLarchey/Murec_Extraction)

6. [CoqGym/goedel](https://github.com/princeton-vl/CoqGym/tree/master/coq_projects/goedel)

7. [formalmetatheory-stoughton](https://github.com/ernius/formalmetatheory-stoughton)

8. [Constructive Analysis of First-Order Completeness](https://github.com/uds-psl/fol-completeness-theorems/tree/master)
