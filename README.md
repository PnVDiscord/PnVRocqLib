# PnVRocqLib

A Rocq library written by members of [PnV Discord Server](https://github.com/PnVDiscord).

- Currently, this library is standalone.

## 1. How to build

```
git clone https://github.com/PnVDiscord/PnVRocqLib.git
cd PnVRocqLib
eval `opam env`
rocq makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile -j
```

### `rocq -v`

```
The Rocq Prover, version 9.1.0
compiled with OCaml 5.3.0
```

## 2. Contents

Our main results are:

- [x] The Kleene fixed-point theorem. (`Theorem lfp_returns_the_least_fixed_point` in [`ClassicalDomainTheory.v`](theories/Math/ClassicalDomainTheory.v))

- [x] The weak completeness of propositional logic. (`Corollary weak_completeness` in [`PropositionalLogic.v`](theories/Logic/PropositionalLogic.v))

- [x] The soundness, completeness, and compactness theorems of propositional logic. (`Theorem the_propositional_soundness_theorem`, `Theorem the_propositional_completeness_theorem`, and `Corollary the_propositional_compactness_theorem` in [`ClassicalPropositionalLogic.v`](theories/Logic/ClassicalPropositionalLogic.v))

- [x] The soundness and countable completeness theorems of first-order logic. (`Theorem HilbertCalculus_sound` and `Theorem HilbertCalculus_countable_complete` in [`ClassicalFol.v`](theories/Logic/ClassicalFol.v))

- [x] The weak normalisation property of STLC. (`Corollary Normalisation_by_Evaluation`) in [`STLC.v`](theories/System/STLC.v)

- [x] The Bourbaki-Witt fixed-point theorem and the geneneralised Kleene fixed-point theorem (`Theorem BourbakiWittFixedpointTheorem` and `Theorem generalised_Kleene_fixedpoint_theorem`) in [`ClassicalSetTheory.v`](https://github.com/PnVDiscord/PnVRocqLib/blob/main/theories/Math/ClassicalSetTheory.v)

### [theories/Control](theories/Control)

- `Category.v` : Basic theory on category.

- `Monad.v` : Basic definitions about monad.

### [theories/Data](theories/Data)

- `Aczel.v` : Aczel's type theoretic interpretation of set theory.

- `Graph.v` : Basic graph theory.

- `ITree.v` : Basic Definitions on interaction tree.

- `NumRepr.v` : Number Representation.

- `Vector.v` : Replaces `Stdlib.Vectors.VectorDef.t`.

### [theories/Flower](theories/Flower)

- `FlowerAxioms.v` : Axioms for the sublibrary `Flower`.

- `FlowerPrelude.v` : The prelude of the sublibrary `Flower`.

### [theories/Index](theories/Index)

- `Index.v` : Accumulates all source files and check their consistency.

### [theories/Logic](theories/Logic)

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

### [theories/Math](theories/Math)

- `BooleanAlgebra.v` : Basic theory on Boolean algebras.

- `ClassicalDomainTheory.v` : Classical domain theory.

- `ClassicalSetTheory.v` : Classical set theory.

- `DomainTheory.v` : Constructive domain theory.

- `OrderTheory.v` : Basic order theory.

- `SetTheory.v` : Constructive set theory.

- `ThN.v` : Basic facts about the natural numbers.

### [theories/Prelude](theories/Prelude)

- `ClassicalFacts.v` : Facts about `CIC + (classic : forall P, P \/ ~ P)`.

- `ConstructiveFacts.v` : Facts about CIC.

- `Notations.v` : Reserves all notations to avoid the conflict.

- `SfLib.v` : A copy of `snu-sf/sflib.v`.

- `Prelude.v` : The prelude.

### [theories/System](theories/System)

- `BasicITreeTh.v` : A basic theory on interaction trees.

- `FolFramework.v` : A First-Order Logic Framework.

- `Lambda1.v` : Basic definitions for Church-style stlc.

- `P.v` : Provides a function `nat -> option string` by base 36.

- `Regex.v` : A theory on regular expression.

- `STLC.v` : Basic theorems for Church-style stlc.

## 3. References

### Source Code

1. [sflib](https://github.com/snu-sf/sflib)
1. [stdpp](https://plv.mpi-sws.org/coqdoc/stdpp)
1. [DmxLarchey/Murec_Extraction](https://github.com/DmxLarchey/Murec_Extraction)
1. [CoqGym/goedel](https://github.com/princeton-vl/CoqGym/tree/master/coq_projects/goedel)
1. [ernius/formalmetatheory-stoughton](https://github.com/ernius/formalmetatheory-stoughton)
1. [uds-psl/Constructive Analysis of First-Order Completeness](https://github.com/uds-psl/fol-completeness-theorems)
1. [snu-sf/Ordinal](https://github.com/snu-sf/Ordinal)
1. [Damhiya/Logos](https://github.com/damhiya/Logos)
1. [Lean Zulip Chat (1)](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Bug.20in.20kernel.20level.20normalization/near/306169266)
1. [DeepSpec/Interaction Trees](https://github.com/DeepSpec/InteractionTrees)

### Literature

1. [A note written by Jayadev Misra](https://www.cs.utexas.edu/users/misra/Notes.dir/KnasterTarski.pdf)
1. [Constructive Completeness Proofs and Delimited Control](https://theses.hal.science/pastel-00530424/)
1. [A Mathematical Introduction to Logic](https://www.amazon.com/Mathematical-Introduction-Logic-Herbert-Enderton/dp/0122384520)
1. [The Lambda Calculus: Its Syntax and Semantics](https://api.pageplace.de/preview/DT0400.9780080933757_A23543814/preview-9780080933757_A23543814.pdf)
1. [The Power of Parameterization in Coinductive Proof](https://plv.mpi-sws.org/paco/ppcp.pdf)

## 4. Thanks to

- [Soonwon Moon](https://sf.snu.ac.kr/soonwon.moon)
- [Hanul Jeon](https://hanuljeon95.github.io)
- [Clare Jang](https://ailrun.github.io)

## 5. Goals 

### Established at 2024-10-16

1. Ordinal Numbers
1. IPO <=> pointed DCPO
1. Regular Language: Regex, ε-NFA, DFA, and Lexer Genrartor
1. LALR(1) CFG: Parser Generator
1. Gödel's Incompleteness Theorem