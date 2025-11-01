# Loom: A Framework for Automated Generation of Foundational Multi-Modal Verifiers

`Loom` is a framework for producing foundational multi-modal verifiers. Main features are:

* Automated weakest precondition generation

* Executable semantics

* Non-Determinism semantics

* Ready-to-use sample verifiers for imperative code with automated and interactive proofs

`Loom` is based on the monadic shallow embedding of an executable program semantics into Lean 4 theorem prover.

For automated weakest precondition generation, `Loom` uses Monad Transformer Algebras.

## Build and Dependencies

To build the project run `lake build` command in terminal from project's root directory.

`Loom` has the following dependencies:

- [Lean 4](https://lean-lang.org/) - foundational program verifier in which the framework was implemented. Version 4.20 is required.

- [Mathlib4](https://github.com/leanprover-community/mathlib4) - Mathlib4 library for Lean, provides necessarily theoretical foundations

- [lean-auto](https://github.com/leanprover-community/lean-auto) - SMT backend for `Velvet`. 
Note that as `lean-auto` depends on `cvc5` which is not available for native Windows, therefore `Velvet` won't work on native Windows as well, but `Loom` is still available (use `lake build Loom` for standalone build)

You need `cvc5` to be on your PATH to run `Velvet` examples.  

## Navigation Guide

The repository consists of 2 key parts:

 - `Loom`, the framework itself

 - `CaseStudies`, examples for deriving and using Program Verifiers powered by Loom

 ### `Loom` folder

This folder contains the theoretical foundation of the framework: 

- typeclass definitions for Ordered Monad Algebras (`MAlgOrdered`)  and Monad Transformer Algebras (`MAlgLift`) in `Loom/MonadAlgebras/Defs.lean`

- instances of Monad Transformer Algebras for key monads with effect (`ExceptT`, `StateT`, `ReaderT`) in `Loom/MonadAlgebras/Instances`

- `NonDetT/NonDetT'` definitions and Weakest Precondition generators for Monad Transformers with Non-Determinisms in `Loom/MonadAlgebras`

- Weakest Precondition generation and theorems for it in `Loom/MonadAlgebras/WP`

Also it provides ready-to-use macros for an imperative `WHILE`-like language.

### `CaseStudies` folder

This folder contains two framework examples powered by Loom: `Velvet` and `Cashmere`.

- `Velvet` is a framework for Dafny-style specification and verification of imperative programs. 

  Theory about separated proofs for termination and correctness in Velvet is in `CaseStudies/Velvet/VelvetTheory.lean`,
  related example file is `CaseStudies/Velvet/VelvetExamples/Total_Partial_example.lean`

  Please refer to `CaseStudies/Velvet/velvet_documentation.md` for detailed documentation about Velvet.

- `Cashmere` is a simple framework used to showcase variety of monadic effects `Loom` can provide.

  Theory about Incorrectness reasoning in Cashmere is located in `CaseStudies/Cashmere/CashmereTheory.lean`,
  related example file is `CaseStudies/Cashmere/CashmereIncorrectnessLogic.lean`

- Both of them are supplied with `loom_solver`, `loom_solve`, `loom_solve!` and `loom_solve?` tactics.

  `loom_solve` tactic produces goals for VCs (each one corresponds to a single `invariant`/`assert`/`ensures` annotation in the program) with human-readable hypotheses and tries to discharge them with `loom_solver`.

  `loom_solver` is a main tactic for discharging VCs. This tactic can be set by user with Lean `macro_rules`:
    ```lean
    macro_rules
    | `(tactic|loom_solver) => `(tactic|aesop)
    ```

  For `Velvet` it is `auto` tactic with hints for closing complex goals, for `Cashmere` it is `aesop` tactic with additional theorems for proof reconstruction.

  `loom_solve!` tactic works similarly to `loom_solve`, but also highlights invariants and pre/post-conditions that were not proven by `loom_solver`.

  `loom_solve?` tactic suggests a sequence of more low-level tactics to get the same result as `loom_solve`.


#### Full list of implemented examples

Examples are organized in directories by their verifier:

- `CaseStudies/Cashmere` - directory with examples from Section 2 of the paper
  - `Cashmere.lean` - definition of the computational monad for `Cashmere` examples as well as correctness proofs for all case studies up to Section 2.6

  - `CashmereIncorrectnessLogic.lean` - example from 2.7: using Angelic Non-Determinism to prove that there exists a bug in a program
- `CaseStudies/Velvet/VelvetExamples` - directory with examples from Section 8 of the paper

  - `Examples.lean` - basic Dafny-like examples (`insertionSort`, `squareRoot`) in `Velvet` with partial correctness semantics

  - `Examples_Total.lean` - similar examples but in Total semantics, also contains a `cbrt` example for manual proof after SMT failure

  - `Total_Partial_example.lean` - concluding functional correctness in total semantics from termination and functional correctness in partial semantics effortlessly for `insertionSort`
  
  - `SpMSpV_Example.lean` - proving sparse matrix multiplication algorithms mixing automated and interactive proof modes with "two-layered paradigm"
