# Loom: A Framework for Foundational Multi-Modal Program Verifiers (Artifact)

[POPL'26 submission #695](https://popl26.hotcrp.com/paper/695)

Loom is a framework for producing foundational multi-modal verifiers. It
provides:

* Automated weakest precondition generation
* Executable semantics
* Semantics for non-determinism
* Ready-to-use sample verifiers for imperative code with automated and
  interactive proofs

Loom is based on the monadic shallow embedding of an executable program
semantics into the [Lean 4 proof assistant](https://lean-lang.org/).

For automated weakest precondition generation, Loom uses Monad Transformer
Algebras.

Loom is licensed under the
[Apache 2.0 license](https://www.apache.org/licenses/LICENSE-2.0) and is
available on GitHub at
[github.com/verse-lab/loom](https://github.com/verse-lab/loom).

## Requirements

We have tested this artifact on:
- `arm64` MacBook Air 2022 with an M2 processor and 16GB of RAM. 
- `amd64` HP Laptop 15-db1xxx 2019 with AMD Ryzen 5 3500U and 16GB of RAM.
We recommend running this artifact on a machine with at least
16GB of RAM. We are also providing a VM with Ubuntu 24.04 LTS for testing on `AArch64` 

## Build and Setup

To build the artifact, you need [VSCode](https://code.visualstudio.com) and
[Lean 4 VSCode extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
installed. Their installation is straightforward and does not require any special
knowledge.

You will also need [cvc5](https://github.com/cvc5/cvc5) installed (we tested
using version 1.3.1) and available on your PATH to run Velvet examples. To do
this, you will need to:

- download an appropriate static version for your OS and processor from
  [this page](https://github.com/cvc5/cvc5/releases)
- find executable `cvc5` under `bin/` subdirectory of the downloaded archive
- ensure that this executable is now on your path
  for MacOS/Linux
  ```bash
  sudo mv /path/to/cvc5 /usr/local/bin
  ```
  check: 
  ```bash
  cvc5 --version
  ```
  The command above should output `cvc5`'s version and additional information.

After verifying that `cvc5` is available, you can open artifact folder in VSCode
and open any Lean file. Press Lean symbol at the top right and then
`Toggle InfoView`. You might need to press `Restart File` button in Lean
InfoView to see the result.

**IMPORTANT** Note that first run (Lean 4 installation) and following build
(after restarting the file) might take some time, usually less than 20 minutes.

After building, you will be able to inspect Lean 4 files and InfoView freely.

### Common Problems

- You might be requested to update `smt` dependency. To do so, in your terminal:
  - change directory to the `Loom` subdirectory of this artifact 
  - type
    ```bash
    lake update smt
    ```
  - reopen VSCode and artifact folder in VSCode
- If build fails, try to:
  - close VSCode
  - in your terminal, change directory to the `Loom` subdirectory of this
    artifact
  - type
    ```bash
    lake clean
    lake exe cache get
    lake build
    ```
    in your terminal
  - reopen VSCode and artifact folder

## Structure and Contents

- `Loom/`: implementation of the framework itself and 2 new verifiers built on
  top of Loom: Velvet and Cashmere
  - `Loom/`: the implementation of Loom framework,
    - `Meta.lean`: definitions for working with Lean 4 environment and 
    `#derive_lifted_wp` command definition
    - `MonadUtil.lean`: `Cont` monad definition
    - `MonadAlgebras/`: Monad Transformer Algebra defintions and lemmas
      - `Defs.lean`: definitions of typeclasses for Monad Transformer Algebra
        and typeclasses
      - `Instances/`: Monad Transformer Algebra and Ordered Monad Algebra
        instances for basic Monad Transformers
        - `Basic.lean`: typeclass instances for `DivM` monad
        - `ExceptT.lean`: typeclass instances for `ExceptT` monad transformer
        - `Gen.lean`: typeclass instances for `Gen` monad
        - `ReaderT.lean`: typeclass instances for `ReaderT` monad transformer
        - `StateT.lean`: typeclass instances for `StateT` monad transformer
      - `NonDetT/`: implementation of a monad transformer for non-determinism
        with loops
        - `Basic.lean`: definition of a monad transformer for non-determinism
          with loops and instances for Monad Transformer Algebra, Ordered Monad
          Algebra typeclasses
        - `Extract.lean`: implementation of executable semantics for
          non-determinism monad transformer
      - `NonDetT'/`: implementation of a monad transformer for non-determinism
        - `Basic.lean`: definition of a monad transformer for non-determinism
          and instances for Monad Transformer Algebra, Ordered Monad Algebra
          typeclasses
        - `Extract.lean`: implementation of executable semantics for
          non-determinism monad transformer
      - `WP/`: lemmas and tactics for Weakest Preconditions and VC generation in
        Loom
        - `Attr.lean`: definitions for working with Lean 4 environment for VC
          generation
        - `Basic.lean`: definition of Weakest Precondition and lemmas about WP
          for basic monad transformers (`StateT`, `ReaderT`, `ExceptT`)
        - `DoNames'.lean`: Lean do-notation extension to enable variables and
          hypothesis naming in verifiers that are built on top of Loom
        - `Gen.lean`: basic `WHILE` language syntax and lemmas for VC generation
          in verifiers that are built on top of Loom
        - `Liberal.lean`: definitions and lemmas for weakest liberal
          precondition
        - `Tactic.lean`: tactics for automatic VC generation for verifiers that
          are built on top of Loom
  - `CaseStudies/`: implementation of Velvet and Cashmere verifiers
    - `Extension.lean`: definitions for keeping track of proof obligations in 
      Cashmere and Velvet
    - `Tactic.lean`: tactics for proof automation in Cashmere and Velvet
    - `TestingUtil.lean`: command for deriving decidability of pre- and post-
      conditions
    - `Theory.lean`: lemmas for arrays and partial sums used by automation
    - `Cashmere/`: Cashmere verifier implementation
      - `Cashmere.lean`: code examples that are verified in Cashmere
      - `CashmereIncorrectnessLogic.lean`: example of using Angelic
        non-determinism for bug finding in Cashmere
      - `CashmereTheory.lean`: theorem about Incorrectness Logic in Cashmere
      - `Syntax_Cashmere.lean`: Cashmere DSL and macros definitions
    - `Velvet/`: Velvet verifier implementation
      - `Std.lean`: typeclasses and macros for arrays used in Velvet programs
      - `Syntax.lean`: Velvet DSL and macros definitions
      - `VelvetTheory.lean`: theorem about deriving total correctness from 
        partial correctness and termination proof
      - `VelvetExamples/`: examples of programs verified in Velvet
        - `Examples_Total.lean`: Insertion Sort, Square Root and Cubic Root
          examples verified in total correctness; manual proof for failed
          automation example
        - `Examples.lean`: Insertion Sort and Square Root examples verified in
          partial correctness; simple testing example
        - `SpMSpV_Example.lean`: Sparse Matrix by Sparse Vector multiplication
          example; 2 layer proof and `triple` reusing example
        - `Total_Partial_example.lean`: example of proving total correctness by
          combining `triple`s about partial correctness and termination
- `Veil/` - Veil version upgraded with Loom

### Definitions and Theorems from Paper Overview (Section 2)

- Code example described in Section 2.2 Fig. 1(b) (Page 4) corresponds to lines
  51-54 of `Loom/CaseStudies/Cashmere/Cashmere.lean`
- Code example described in Section 2.2 Fig. 1(c) (Page 4) is generated
  automatically by Loom therefore is not present explicitly
- Code example described in Section 2.3 Fig. 1(d) (Page 4) corresponds to lines
  62-73 of `Loom/CaseStudies/Cashmere/Cashmere.lean`
- Code example described in Section 2.4 corresponds to lines 82-94 of
  `Loom/CaseStudies/Cashmere/Cashmere.lean`
- Code example described in Section 2.5 Fig. 3(a) (Page 6) corresponds to lines
  102-119 of `Loom/CaseStudies/Cashmere/Cashmere.lean`
- Code example described in Section 2.6 Fig. 3(c) (Page 6) corresponds to lines
  127-144 of `Loom/CaseStudies/Cashmere/Cashmere.lean`
- Code example described in Section 2.7 corresponds to lines 33-48 of
  `Loom/CaseStudies/Cashmere/CashmereIncorrectnessLogic.lean`

### Definitions and Theorems from Section 3

- Definition (4) on line 404 for WP defined in Loom corresponds to lines 25-27
  of `Loom/Loom/MonadAlgebras/WP/Basic.lean`
- Definition (5) on lines 405-406 for WP defined in Loom corresponds to lines
  39-41 of `Loom/Loom/MonadAlgebras/WP/Basic.lean`
- Definition (8) on lines 453-454 for WP defined in Loom corresponds to lines
  21-22 of `Loom/Loom/MonadAlgebras/WP/Basic.lean`
- Definition (9) on line 456-457 for WP defined in Loom corresponds to lines
  48-52 of `Loom/Loom/MonadAlgebras/WP/Basic.lean`
- Definition 3.1 (Monad Algebra) on lines 478-481 corresponds to lines 51-56 of
  `Loom/Loom/MonadAlgebras/Defs.lean`
- Definition 3.2 (Ordered Monad Algebra) on lines 491-495 Fig.4 (Page 14)
  corresponds to lines 74-79 of `Loom/Loom/MonadAlgebras/Defs.lean`
- Definition (10) on lines 503-504 corresponds to lines 58-59 of
  `Loom/Loom/MonadAlgebras/Defs.lean`
- Theorem 3.3 (Properties of WP derived from Ordered Monad Algebra) on lines
  510-513 corresponds to: `wp` on line 19 of
  `Loom/Loom/MonadAlgebras/WP/Basic.lean` defined via `MAlg.lift` on lines 58-59
  of `Loom/Loom/MonadAlgebras/Defs.lean` by instance in lines 61-62 of
  `Loom/Loom/MonadAlgebras/Defs.lean`, then lemmas for `wp` are proven in file
  `Loom/Loom/MonadAlgebras/WP/Basic.lean`
  - (4) on lines 25-27
  - (5) on lines 39-41
  - (9) on lines 48-52
- Formalization of (15-17) on lines 570-573 as a Loom lemma corresponds to lines
  471-473 in file `Loom/Loom/MonadAlgebras/WP/Basic.lean`
- Definition 3.4 (Monad Transformer Algebra) on lines 624-629 Fig.5 (Page 14)
  corresponds to lines 193-199 in file `Loom/Loom/MonadAlgebras/Defs.lean`

### Definitions and Theorems from Section 4

- `#derive_lifted_wp` definition on lines 703-704 corresponds to lines 431-450
  in file `Loom/Loom/Meta.lean`

### Definitions and Theorems from Section 5

- Definition 5.4 (Partial Monad Algebra) on lines 791-793 corresponds to lines
  118-122 in file `Loom/Loom/MonadAlgebras/Defs.lean`
- The claim about Partial Monad Algebra preservation on lines 803-809 is proven
  in corresponding files:
  - `ExceptT`: lines 164-169 `Loom/Loom/MonadAlgebras/Instances/ExceptT.lean`
  - `ReaderT`: lines 64-79 `Loom/Loom/MonadAlgebras/Instances/ReaderT.lean`
  - `StateT`: lines 61-76 `Loom/Loom/MonadAlgebras/Instances/StateT.lean`

### Definitions and Theorems from Section 6

- Definition of a monad transformer for non-determinism Fig. 7a (Page 17)
  corresponds to
  - lines 15-19 in file `Loom/Loom/MonadAlgebras/NonDetT/Basic.lean`
  - lines 14-17 in file `Loom/Loom/MonadAlgebras/NonDetT'/Basic.lean`
- Definition of a monad algebra instance for non-determinism Fig. 7b (Page 17)
  corresponds to
  - `Loom/Loom/MonadAlgebras/NonDetT/Basic.lean`
    - lines 83-90 and 120-121 (for `PartialCorrectness DemonicChoice`)
    - lines 247-254 and 282-283 (for `PartialCorrectness AngelicChoice`)
    - lines 408-415 and 446-447 (for `TotalCorrectness DemonicChoice`)
    - lines 571-578 and 606-607 (for `TotalCorrectness AngelicChoice`)
  - `Loom/Loom/MonadAlgebras/NonDetT'/Basic.lean`
    - lines 72-75 and 101-102
- Definition (20) on lines 850-851 corresponds to
  - lines 56-57 in file `Loom/Loom/MonadAlgebras/NonDetT/Basic.lean`
  - lines 53-54 in file `Loom/Loom/MonadAlgebras/NonDetT'/Basic.lean`
- Definition (21) on lines 869-870 corresponds to 
  - line 109 in file `Loom/Loom/MonadAlgebras/NonDetT/Basic.lean`
  - line 109 in file `Loom/Loom/MonadAlgebras/NonDetT'/Basic.lean`
- Definition of Theorem 6.1 (Soundness of `NonDetT.run`) corresponds to
  - `NonDetT`: note that definition of `NonDetT.run` on lines 246-248 of file
    `Loom/Loom/MonadAlgebras/NonDetT/Basic.lean` is equal to the definition of
    `NonDetT.extract` on lines 223-225 of the same file. Theorem is proven on
    lines 431-436 of file `Loom/Loom/MonadAlgebras/NonDetT/Basic.lean`
  - `NonDetT'`: note that definition of `NonDetT.run` on lines 233-235 of file
    `Loom/Loom/MonadAlgebras/NonDetT'/Basic.lean` is equal to the definition of
    `NonDetT.extract` on lines 210-212 of the same file. Theorem is proven on
    lines 399-404 of file `Loom/Loom/MonadAlgebras/NonDetT'/Basic.lean`

Weakest Liberal Preconditions definitions and lemmas can be found in file
`Loom/Loom/MonadAlgebras/WP/Liberal.lean`

### Definitions and Theorems from Section 7

- definitions on Fig. 9 (Page 20) can be found in file
  `Veil/Veil/Theory/Defs.lean`
  - `VeilM` definition corresponds to lines 48-49
  - `VeilM.succeedsWhenIgnoring` corresponds to lines 151-152
  - `VeilM.meetsSpecificationIfSuccessful` corresponds to lines 87-88
  - `VeilM.toTwoState` corresponds to lines 103-104
- NOPaxos Case Study can be found in `Veil/Examples/NOPaxos` directory
  - Implementation of the protocol can be found in file
    `Veil/Examples/NOPaxos/NOPaxos.lean`
    - Fig. 10(a) (Page 21) corresponds to lines 9-50
    - Fig. 10(b) (Page 21) corresponds to lines 110-117
  - Simulation procedure described on lines 1006-1017 is done in file
    `Veil/Examples/NOPaxos/NOPaxosTest.lean`

### Definitions and Theorems from Section 8

Velvet verifier implementation can be found in `Loom/CaseStudies/Velvet`
directory

Verified examples can be found in `Loom/CaseStudies/Velvet/VelvetExamples`
directory

- definition of `VelvetM` on lines 1053-1054 corresponds to line 3 in file
  `Loom/CaseStudies/Velvet/VelvetTheory.lean`
- `insertionSort` implementation Fig. 11 (Page 22) corresponds to lines 65-98 in
  file `Loom/CaseStudies/Velvet/VelvetExamples/Examples_Total.lean`
- "interface" for Lean `Array` described on lines 1062-1067 can be found on
  lines 14-62 in file `Loom/CaseStudies/Velvet/Std.lean`
- testing example described on lines 1067-1074 can be found on lines 103-112 in
  file `Loom/CaseStudies/Velvet/VelvetExamples/Examples.lean`
- Lean 4 goal on Fig. 12 (Page 22) can be produced by commenting out line 94 in
  file `Loom/CaseStudies/Velvet/VelvetExamples/Examples_Total.lean` and then
  checking Lean Infoview after `loom_solve!` on line 98 Syntax highlighting will
  appear on line 80 of the same file
- proof of lemma on lines 1096-1098 can be found on lines 181-190 in file
  `Loom/CaseStudies/Velvet/VelvetTheory.lean`
- `SpMSpV` example described in Section 8.2 corresponds to file
  `Loom/CaseStudies/Velvet/VelvetExamples/SpMSpV_Example.lean`
  - method itself can be found on lines 194-224
  - `SpMSpV_pure` helper function corresponds to `spv_dot` defined on lines
    152-163
  - specification described on Fig. 13 (Page 23) is obtained in theorem
    `SpMSpV_correct_triple` on lines 764-789

## Badge Checklist

### Functional

- **(Completeness)** All examples mentioned in the paper have correspondning
  reference to specific files in source code.
  - examples from Section 2 are available in `Loom/CaseStudies/Cashmere`
    directory
  - key theoretical definitions mentioned in Section 3 are available in
    `Loom/Loom` directory and README file points out the exact corresponding
    locations in source code
  - implementation of divergence without co-inductive definitions has clear
    references in README to actual proofs in source code
  - non-determinism monad transformer implementation has detailed code
    references in README for definitions and proofs
  - Veil framework upgrade presented in the paper is available and key features
    (such as simulation) have references in README
  - examples for Velvet verifier have clear mapping to concrete lines in source
    code
- **(Consistency)** The artifact supports the claims made in the paper. All the
  examples powered by new framework are present in the artifact for inspection.
  README provides a guide on how to reproduce interactive features in Velvet.
  All theoretical claims made in the paper are formalized in Lean 4.
- **(Documentation)** README provides clear mapping from statements in the paper
  to actual lines in source code as well as general structure and file
  organization. This allows to assess main contributions and navigate through
  examples. Both Cashmere and Velvet provide set of non-trivial programs
  verified smoothly by using Loom and comments that explain key features of the
  verifiers.

### Reusable

- **(Reusability beyond the paper)** Loom can be used to build new verifiers. To
  use Loom as a dependency, please check **Reusability Guide**. Velvet can be
  used directly to verify imperative programs by extending existing example
  files or creating new ones in `Loom/CaseStudies/Velvet/VelvetExamples`
  directory. Veil and its new features can be used to verify complex distributed
  protocols. For specific instructions please refer to project's README.
- **(Extensions)** The artifact is publicly available on GitHub.
- **(Instructions)** The artifact provides clear instructions for build and
  installation of dependencies.
- **(Proof reusability)** Proofs in the artifact can be reused to build new
  verifiers (Cashmere, Velvet and Veil are such examples). Velvet and Veil can
  be used as standalone verifiers to automatically verify imperative programs
  and distributed protocols respectively.
- **(Dependencies)** The only dependencies are
  - Lean 4 itself
  - Lean 4 Mathlib and `lean-auto` for proof automation, automatically
  installed when building Loom
  - `cvc5`, whose installation process is described in the README

- **(Proof completeness)** Proofs do not depend on `sorry` or `admit` and are
  accepted by Lean 4.

## Reusability Guide

Loom is [publicly available](https://github.com/verse-lab/loom) under Apache 2.0
license.

To use Loom in your project, add the following to your `lakefile.lean`:

```lean
require "verse-lab" / "loom" @ git "main"
```

Or add the following to your `lakefile.toml`:

```toml
[[require]]
name = "Loom"
git = "https://github.com/verse-lab/loom.git"
rev = "main"
```

- to get started with verifiers that are built on top of Loom, we recommend
exploring `CaseStudies/VelvetExamples` directory or
`CaseStudies/Cashmere/Cashmere.lean` file.
- to understand how Loom works internally we recommend exploring `Loom` directory.

### I want to build a verifier similar to Velvet/Cashmere. How to proceed?

To do this, you will need to:
- add Loom as a dependency in your project by following the instructions above
- create a directory for your verifier
- create a file which will include metatheory for your verifier. In particular,
  you will need to define your monad stack to account for different effects you
  would like to support. Example monad stacks:
  - `VelvetM α := NonDetT DivM α`
  - `CashmereM := NonDetT (ExceptT String (StateT Bal DivM))`
- if you want to have custom effects that are not implemented in public Loom
  version, you will need to:
  - express your effect as a monad transformer.
  - provide `MAlgOrdered` instance appropriate for your transformer (you can
    check Loom's implementation for basic effects for reference).
  - provide `MAlgLift` instance appropriate for your transformer (you can
    check Loom's implementation for basic effects for reference).
  - provide lemmas about `WPGen` similar to ones defined in
    `Loom/Loom/MonadAlgebras/WP/Gen.lean`. This is crucial for smooth VC
    generation in your verifier.
- copy `Loom/CaseStudies/Cashmere/Syntax_Cashmere.lean` or
  `Loom/CaseStudies/Velvet/Syntax.lean` to your directory. This file will define
  most of macros (and therefore most of the syntax) for your verifier. Adjust
  the file for your needs by changing how `method` and `prove_correct`
  elaboration works (in case you copied Velvet file).
- create a Lean file with examples you would like to verify. Import the root of
  `Loom/CaseStudies`, your syntax file and your metatheory file.
- you might need to use `#derive_lifted_wp` command to use your `WPGen` lemmas
  for effects that are not on top of monad stack. See
  `Loom/CaseStudies/Cashmere/Cashmere.lean` for an example.
- (Optional) customize your automation by changing `loom_unfold` and
  `loom_solver` tactics in your syntax file.