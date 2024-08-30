# PnVRocqLib

A Coq library written by members of PnV Discord Server.

Currently, this library is standalone.

## Quick Start

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

## Contents

### Data

- `Aczel.v` : Aczel's Type Theoretic Interpretation of Set Theory.

- `Vector.v` : Replaces `Coq.Vectors.VectorDef.t`.

### Logic

- `BasicFol.v` : Basic definitions of First-Order Logic

- `ClassicalFol.v` : Meta-theories on Classical First-Order Logic.

- `ClassicalPropositionalLogic.v` : The Soundness, Completeness and Compactness Theorem for PropositionalLogic.

- `MuRec.v` : Basic facts on μ-recursive functions.

- `PrimRec.v` : Basic facts on primitive recursive functions.

- `PropositionalLogic.v` : Contructive meta-theory on the Propositional Logic.

### Index

- `Index.v` : Accumulates all source files and check their consistency.

### Math

- `BooleanAlgebra.v` : Basic theory on Boolean Algebras.

- `ClassicalDomainTheory.v` : Classical domain theory.

- `DomainTheory.v` : Constructive domain theory.

- `OrderTheory.v` : Basic order theory.

- `ThN.v` : Basic facts on the natural numbers.

### Prelude

- `Classical.v` : Facts about classical logic.

- `ConstructiveFacts.v` : Facts on CIC.

- `Notations.v` : Reserves all notations to avoid the conflict.

- `SfLib.v` : The copy of `snu-sf/sflib.v`. See `References`.

- `Prelude.v` : The prelude code.

## References

1. [sflib](https://github.com/snu-sf/sflib)

2. [stdpp](https://plv.mpi-sws.org/coqdoc/stdpp)

3. [A note written by Jayadev Misra](https://www.cs.utexas.edu/users/misra/Notes.dir/KnasterTarski.pdf)

4. [Constructive Completeness Proofs and Delimited Control](https://theses.hal.science/pastel-00530424/)

5. [Murec_Extraction](https://github.com/DmxLarchey/Murec_Extraction)

6. [CoqGym/goedel](https://github.com/princeton-vl/CoqGym/tree/master/coq_projects/goedel)

7. [formalmetatheory-stoughton](https://github.com/ernius/formalmetatheory-stoughton)
