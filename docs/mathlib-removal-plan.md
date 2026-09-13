> Notation update: the implementation now retains the conventional mathlib
> symbols through `open scoped Loom.Order`. References below to subscripted
> symbols describe the original plan and have been superseded.

Remove mathlib from Loom while preserving its generic abstractions.

This plan targets the Veil-focused Loom checkout audited at `12b4f9b`, on Lean
4.32.0. The outcome is a standalone Loom package with arbitrary assertion
languages, monads, monad transformers, candidate providers, and log types. A
separate integration package supplies interoperability with mathlib. Preserving
those abstractions permits changes to the foundational types in public
signatures; it does not promise unchanged source compatibility with mathlib's
classes or its transitively exported declarations.

The implementation should stay on Lean 4.32.0 during this migration. Toolchain
upgrades and unrelated refactors would make failures harder to attribute.

Implementation includes the dependency trim, regression infrastructure,
standalone controls, and the assertion-order hierarchy with generic models
and explicit mathlib conversions. The monad utilities and specification
interfaces now use the standalone foundations, and extraction uses the new
writer and persistent-log types. Progress and remaining work are recorded in
`docs/mathlib-removal-progress.md`. The algebra and WP/WLP assertion proofs
still require mathlib; their continuation helpers are temporarily isolated
until those consumers are ported.

**The acceptance criteria apply to the complete library.**

| Requirement | Evidence required before completion |
| --- | --- |
| No mathlib dependency in the standalone package | Fresh resolution and build without mathlib in the manifest, package directory, or module search path |
| Generic assertion languages remain supported | Abstract theorems retain their assumptions; a non-Boolean complete-lattice example and a separate Boolean example compile |
| Existing semantics remain supported | Demonic and angelic choice, WP/WLP, partial and total correctness, effects, and extraction correctness all compile with proved laws |
| Executable behavior is preserved | Regression cases check result lists, order, multiplicity, logs, exceptions, and sharing |
| Native consumers remain supported | `lake build`, `lake build Loom:static`, and a consumer with `precompileModules := true` succeed |
| Veil remains supported | Its relevant correctness, extraction, and performance tests pass against the migrated Loom |
| Optional mathlib integration is usable | A separate package builds with mathlib and Loom together, including explicit bridge and inference tests |
| Proof integrity is maintained | No new `sorry`, `admit`, or unchecked axioms; intended uses of classical logic remain explicit |

Veil's own mathlib removal is outside this plan. Its current direct mathlib
imports make coexistence an immediate requirement, even before an entirely
mathlib-free Veil is attempted. Veil has no `require mathlib` of its own: its
lakefile requires only lean-smt and Loom, and its manifest records mathlib as
inherited through Loom. Once Loom drops the requirement, Veil must add a direct
`require mathlib` pinned to the same revision and regenerate its manifest, or
its own imports stop resolving. Commented-out unfinished theorems in Loom are
not part of the existing functionality to restore.

While Veil keeps mathlib, this work does not eliminate Veil's package dependency.
Its net build and import footprint must be measured: removing Loom's imports
can change the combined import graph, while the replacement adds its own code.
The standalone package also becomes usable by consumers that do not want mathlib; its CI
no longer needs a mathlib cache, its toolchain upgrades stop waiting on mathlib
releases, and Veil's later removal can focus on its own dependencies. The audit
found 23 direct mathlib import statements under `Veil/`, plus one in `Examples/`;
these counts do not measure Veil's transitive or implicit use of mathlib.
If none of those outcomes is wanted, the cheaper trim described below is the
better stopping point.

**The existing audit establishes feasibility, not completion of the port.**

The baseline has 15 implementation modules and one root module, approximately
3,700 lines. There are 19 mathlib import statements in nine files, naming 11
distinct modules. The compiled environment loads 440 mathlib modules. Loom's
compiled declarations directly reference 229 distinct mathlib declarations
from 28 defining modules; 191 are from order theory. These counts include
generated declarations and instance projections, and do not capture all
tactic, syntax, attribute, or transitive proof dependencies.

The baseline source-level inventory includes the following active uses, with
comments excluded. From mathlib: `introv` (41), `split_ifs` (1), `congr!` (4),
and the `ℕ` (14) and `Type*` (1) notations. From Aesop: `aesop` (4). From Batteries:
`trans` (8) and `on_goal` (2); `trans` also leaves `Trans.simple` in four proof
terms, so it is not purely a source-level dependency. Commands and attributes
also need review, including Batteries' `alias` command. Many proofs succeed because mathlib tags
lemmas such as `le_top`, `bot_le`, `sup_le_iff`, `le_inf_iff`, `iSup_le_iff`,
and `iSup_congr_Prop` as `simp` lemmas. The replacement hierarchy must support
the intended simplification behavior as well as the named mathematical laws.

Both baseline build targets passed. An isolated experiment removed the tree
import, replaced the `FinEnum` candidate fallback with exhaustive-list
enumeration, provided a local flat-map congruence lemma, and repaired proofs
using a transitive associativity instance. All 16 modules compiled, and loaded
mathlib modules fell from 440 to 224. That experiment did not validate native
builds, downstream compatibility, or performance. Separate small probes showed
that continuations, candidate enumeration, and the extraction's two mathlib
helpers can compile using Lean alone.

That trim should land as its own increment rather than remain a probe. It
removes the two imports that contribute no declarations
(`Mathlib.Data.Tree.Basic` and `Mathlib.Logic.Function.Basic`), moves the
`FinEnum` fallback out, and replaces the two meta helpers and `introv`. These
are small changes requiring targeted proof and extraction checks. Moving the
fallback changes instance availability, so its adapter and migration guidance
must ship in the same increment. The import closure of `Mathlib.Data.FinEnum`
overlaps heavily with the order imports; closure sizes are not exclusive
contributions. The isolated experiment establishes the net reduction. Landing the trim first gives an immediate
halving of the footprint and a cleaner baseline for the port, and remains
worthwhile even if the full removal is later deferred.

**The package and API design should follow these decisions.**

The root `Loom` package should target Lean/Std alone. Replace the few uses of
Aesop and Batteries conveniences with direct proofs or core APIs. A small
external dependency is acceptable only if implementation reveals a concrete
maintenance benefit; it must itself be mathlib-free. No substantial tactic
framework should be copied merely to retain a handful of tactic invocations.

Own the assertion hierarchy under `Loom.Order`, rather than directly adopting
`Std.Internal.Do.Order` as Loom's public foundation. The pinned standard library
provides useful reference implementations, but its internal API, different
order hierarchy, and different reduction behavior would otherwise become
constraints on Loom. Continue using Lean's existing `Lean.Order.CCPO`,
`MonoBind`, and `partial_fixpoint` for computation domains.

Use namespaced declarations for the new foundational objects. In particular,
do not redefine global mathlib names such as `CompleteLattice`, `ContT`,
`WriterT`, `Monoid`, or `Set`. Preserve existing Loom-owned declaration names
and module paths where practical, including `MAlg`, `MAlgOrdered`, `wp`,
`NonDetT`, `Candidates`, and the public extraction tactics. Existing global
helpers such as `Cont.inv` will necessarily move with their carrier type;
document those changes explicitly.

Let Loom's assertion order own its relation. Do not introduce unconditional
global `LE Prop` or function-order instances that compete with mathlib's
instances. Use scoped Loom notation, with `⊑ₗ` for assertion entailment, and
qualified operation names in integration code. Check the scope of lattice and
quantifier notation in a mixed mathlib/Loom file before using it throughout the
port. Lean's computation-domain relation must remain distinguishable from
assertion entailment.

Represent subsets needed for completeness and chain statements as predicates
`α → Prop`. Provide namespaced helpers only when needed; do not recreate the
general mathlib set API. Arbitrary indexed infima and suprema should be
derived from suprema/infima of predicate-defined ranges. This supports indices
in arbitrary universes and `Sort`, including proposition indices, without
putting a universe-polymorphic quantifier field in each lattice instance.

Keep small assumptions small: preorder-only specifications, Boolean
continuation inversion, complete-lattice monad algebras, and complete-Boolean
results must remain separate. Proposition embedding should retain lightweight
order/top/bottom assumptions. Do not strengthen all interfaces to a complete
Boolean algebra, add decidable equality, or restrict arbitrary choices to
finite types for implementation convenience.

Use explicit operation fields where their reduction behavior matters. In
particular, instances for `Prop` and dependent functions should reduce to the
expected logical and pointwise operations. Boolean implication should be an
operation with its defining law, allowing the `Prop` instance to use `p → q`
directly. Defining every operation through classical choices of bounds would
turn many current reductions into additional proof obligations and could
complicate Veil's normalization.

Keep the mathlib adapter in a separate Lake package, provisionally under
`integrations/mathlib/`, exporting `LoomMathlib.*`. The root package must not
require it. During repository development, the integration package can depend
on the root by a relative path. Before release, test a consumer's actual Git
dependency arrangement; use a separately published integration repository if
the intended nested-package layout cannot be consumed reliably. This is a
packaging verification task, not a reason to restore mathlib to the root.

**The proposed module boundaries keep computational code independent of assertion proofs.**

| Proposed module or directory | Responsibility |
| --- | --- |
| `Loom/Order/Defs.lean` | Relation, preorder, partial order, bounds, lattice operations, and laws |
| `Loom/Order/CompleteLattice.lean` | Arbitrary predicate-indexed bounds, indexed operations, and core lemmas |
| `Loom/Order/BooleanAlgebra.lean` | Boolean operations, implication, complement, and complete-Boolean support |
| `Loom/Order/Instances.lean` | `Prop`, dependent functions, and required wrapper instances |
| `Loom/Control/Cont.lean` | Standalone continuation transformer and lawful monad API |
| `Loom/Control/Log.lean` | Generic identity/combination operations and their laws |
| `Loom/Control/Writer.lean` | Generic writer transformer and lawful instances |
| `Loom/Util/List.lean` | The small missing list lemmas actually used by extraction |
| `Loom/Util/Meta.lean` | Extraction helpers implemented using core Lean |
| Existing `Loom/MonadAlgebras/**` | Migrated algebras, semantics, and extraction |
| `integrations/mathlib/LoomMathlib/**` | Explicit order, monad, log, and enumeration bridges |
| `LoomTest/**` and consumer fixtures | Genericity, behavior, dependency, and native-consumer checks |

These are responsibility boundaries, not a requirement to manufacture a file
for every abstraction. Small adjacent pieces can share a file. Avoid moving
the existing extraction entry point as part of this work.

**1. Record the compatibility baseline and make the audit reproducible.**

Preserve a compact declaration-to-dependency inventory and the script used to
generate it in the repository's development tooling. The generator itself
should use Lean APIs, importing the current Loom; its usefulness must survive
mathlib removal. Record separate categories for types, proof terms, executable
definitions, metaprograms, and source-only conveniences. Include the tactic
and notation inventory above. Seed the required simplification lemmas from
compiled proof dependencies and targeted simplifier traces, and investigate
failures during the port. Removing individual simp lemmas can help diagnose a
specific failure but is not an exhaustive upfront audit requirement. Do not treat a count of directly referenced
constants as the amount of code to vendor.

Record current signatures and typeclass assumptions for the algebra families,
logic lifts, correctness theorems, extraction constraints, and candidate
interfaces. Record representative normalization results and executable outputs
before replacing definitions. In Veil, identify the declarations that unfold
Loom internals, especially its action semantics and extraction implementation.
Some Veil proofs unfold mathlib's lattice itself rather than Loom's API and
will break as soon as Loom's assertion order is no longer mathlib's: known
cases are `VeilM.wp_iInf` (unfolds `iInf` and `sInf`),
`VeilM.raises_true_imp_wp_eq_angel_fail_iwp` (`Pi.compl_def`, `compl_iInf`,
`himp_eq`, `inf_comm`), and the `wp_pick` rewrites in `Semantics/WP.lean`
(`Set.mem_range`, `top_le_iff`). Record the full list. Save the exact Veil
revision and commands used for downstream comparison.

Create a small set of regression fixtures around observable behavior rather
than snapshots of every generated proof term. Establish cold and warm build
measurements and representative extraction timings with the same toolchain
and machine; imported-module counts alone are not performance measurements.

Exit condition: the baseline builds, observed behavior is recorded, and the
public interfaces whose assumptions must remain stable have an explicit
migration map.

**2. Implement and validate the new order foundation before porting consumers.**

Implement the following layers, each building on the preceding laws without
unnecessary assumptions:

| Layer | Required surface |
| --- | --- |
| Preorder and partial order | Relation, reflexivity, transitivity, antisymmetry |
| Bounds and lattice | Top, bottom, binary meet/join, universal properties |
| Complete lattice | Chosen infimum/supremum of every predicate-defined subset and their bound laws |
| Indexed operations | `iInf`, `iSup`, bounded and dependent versions, arbitrary index universes |
| Boolean algebra | Complement, distributivity, implication, and their laws |
| Complete Boolean algebra | Coherent completeness and Boolean structure, with required infinite-distribution lemmas proved |

Keep all shared order and operation fields coherent when combining class
layers. In particular, test the paths from a complete Boolean algebra to its
partial order and binary lattice operations. A short hierarchy with explicit
constructors is preferable to copying mathlib's many intermediate classes.

For the Boolean layer, prove the finite-meet/arbitrary-join distributivity and
its dual needed by complete Boolean reasoning. Do not accidentally require
the stronger arbitrary-meet/arbitrary-join interchange property or atomicity;
the existing `CompleteBooleanAlgebra` does not require those stronger laws.

Build only the lemma families needed by Loom: entailment and bounds;
meet/join introduction and elimination; associativity, commutativity, and
distributivity; complement and implication; indexed introduction/elimination,
monotonicity, congruence, exchange, and empty/constant cases; proposition and
pointwise simplification. Tag the new lemmas for `simp` to match the mathlib
simp set the current proofs depend on, as recorded in increment A; a
hierarchy with the right lemmas but the wrong simp attributes fails `simp`
calls in bulk across `Liberal.lean` and `NonDetT'`. Translate uses of generic
disjointness into direct Boolean identities where this avoids an otherwise
unused class hierarchy.

Provide `Prop`, dependent-function, and necessary continuation/identity-wrapper
instances. Cover nested state/reader predicates, not just one function arrow.
Verify that computation remains reducible where existing code expects `rfl`.

As an early design test, construct an explicit conversion from a mathlib
complete lattice into the new interface in the separate integration package.
Do the same for complete Boolean algebras. This catches accidental stronger
assumptions and operation mismatches before hundreds of proofs are migrated.

Exit condition: the foundation compiles without mathlib, abstract law proofs
pass, a non-Boolean finite chain is supported, a Boolean model is supported,
and both can coexist with mathlib through explicit conversions.

**3. Replace continuation, logging, and writer foundations.**

Implement `Loom.ContT r m α := (α → m r) → m r` and `Loom.Cont r α` with the
existing universe generality, pure/bind behavior, `run`, extensionality, and
lawful monad proofs. Add precisely the lift support used by Loom and exposed
to consumers. Port `W`, monotonicity, and continuation inversion to these
types; keep their current assumption levels.

Implement a small generic logging algebra with an identity and combination
operation, associativity, and left/right identity laws. Keep arbitrary log
types supported. Lists receive the empty-list/append instance. Prove the
persistent-log monad laws using these laws directly; do not require
commutativity. Test with distinct log entries so a reversed append is visible.

Implement `Loom.WriterT ω m α` using the existing result/log component order,
with map, pure, bind, `run`, and lawful instances. Preserve generic writer
support even though Veil's main path uses persistent list logs. Keep executable
definitions computable; classical assertion operations must not leak into
enumeration or execution.

Exit condition: these modules compile with core Lean dependencies, preserve
the intended equations and universe parameters, and their generic laws and
representative execution cases pass.

**4. Port monad algebras and effect instances in dependency order.**

Migrate `MonadUtil.lean` and `SpecMonad.lean`, followed by
`MonadAlgebras/Defs.lean`, then `Instances/Basic.lean`, `ExceptT.lean`,
`StateT.lean`, and `ReaderT.lean`. Keep the ordinary `MAlg` interface independent
of order assumptions. Preserve `outParam`/`semiOutParam` behavior unless a
specific inference problem requires a documented adjustment.

Port proposition embedding and the logic-lifting classes. Replace the `Set`
arguments in chain statements with predicates, and connect them directly to
Lean's existing computation-domain APIs. Keep the assertion lattice and
computation-domain order separate. Audit bridge instances for `Id` and
continuations rather than carrying every existing workaround over blindly.

Use explicit instances for difficult composition tests: reader over state,
exception handling with success and failure interpretations, and algebra
lifts through a transformer stack. Verify a custom complete-lattice assertion
language in addition to `Prop`. Existing signatures should undergo mechanical
foundational-name changes rather than additional hypotheses.

Exit condition: every algebra and effect module compiles against the new
foundation, and generic instance resolution succeeds for representative
transformer stacks.

**5. Port WP, WLP, nondeterminism, and their simplification interface.**

Migrate `WP/Basic.lean`, then `WP/Liberal.lean`, then `WP/Attr.lean` and
`WP/Tactic.lean`, followed by `NonDetT'/Basic.lean`. Keep all active theorems
proved. Rewrite proof dependencies incrementally, adding a reusable order
lemma only when its role is clear.

Preserve the current distinctions between total and partial correctness,
exception-as-success and exception-as-failure, and demonic and angelic choice.
Check empty choices explicitly: empty infima give top and empty suprema give
bottom. Preserve the `Nonempty` conditions on deterministic preservation of
indexed operations. Do not infer behavior for empty families from a theorem
that currently excludes them.

Re-establish `loomLogicSimp` and the intended normalization to logical
connectives for proposition-valued state predicates. Use selective simp rules
to avoid rewrite loops or premature expansion of abstract predicates. Keep
the existing loop mechanism based on `partial_fixpoint`; port its assertion
proofs without replacing its domain construction.

Exit condition: generic WP/WLP and nondeterminism theorems compile, their
predicate specializations normalize as expected, and representative Veil
verification examples can be elaborated using the new logical interface.

**6. Remove finite-enumeration, writer, and proof dependencies from extraction.**

Keep `Candidates`, `PartialCandidates`, `ExtCandidates`, and their contracts.
Move the `FinEnum` fallback to the mathlib integration package. Avoid adding a
second mandatory enumeration abstraction: callers can already supply
`Candidates`, and Veil already supplies it from `Veil.Enumeration`. If a
standalone convenience helper is useful, make it construct candidates from
an exhaustive list and its proof, without a mathlib finite-type interface.

Port `ExtractListCore.lean` onto the new assertion, logging, and writer APIs.
Retain `TsilT`, persistent logs, effect mappings, distributive operations, and
their generic correctness interfaces. Supply the small missing list lemmas.
Replace proofs that rely on hidden monoid instances with explicit local laws.
Remove the unused tree and `Function.Basic` imports if the trim increment has
not already done so.

Port `ExtractList.lean` and both directions of extraction refinement. Keep
sound partial candidates distinct from complete candidates; equality of
semantics must continue to require the appropriate completeness/equality
premises. Preserve support for non-enumerable source choices where extraction
is supplied with a suitable candidate provider.

Implement the target helper with metavariable instantiation and annotation
cleanup, preserving its current absence of weak-head normalization. Implement
application-argument replacement with core expression APIs. Test the intended
in-bounds argument update used by extraction. Keep public tactic names and
configuration stable, including `extract_list_tactic`, `extract_let_step`,
`multiextracted`, and `shareValueLets`.

Use fully qualified quotations for renamed foundational declarations.
Preserve join-point abstraction, source/target separation, local certificate
reuse, ordinary-value-let handling, and the extracted-value simplification
procedure. A tactic that proves the right result but duplicates continuations
does not meet the behavioral requirement.

Exit condition: the complete Loom import graph compiles using only the new
foundation; candidate, log, and sharing regression tests pass; no explicit
Mathlib import remains in the root source tree.

**7. Complete mathlib interoperability and migrate Veil.**

The integration package should provide explicit conversion constructors for
mathlib preorder/lattice/Boolean structures and monoids. Supply conversions
for continuation and writer values, prove preservation of pure/bind/run, and
restore the `FinEnum` candidate fallback with its existing enumeration order.
Prove that corresponding assertion operations and entailment agree.

Start with explicit conversions. Add opt-in scoped instances only where tests
establish coherence with Loom's direct `Prop` and function instances. Do not
install both directions as automatic instances: conversion loops and competing
instance paths would undermine the migration. Where unavoidable, a type
wrapper should make the chosen instance explicit.

Document the public signature migration, including namespaced continuations
and writers, assertion relations, generic log instances, and moved helper
lemmas. The adapter provides semantic interoperability, not a blanket promise
that downstream proofs unfolding mathlib implementation details will compile.

Update Veil in an isolated writable checkout when implementation reaches this
stage. First add a direct `require mathlib` to Veil's lakefile at the revision
Loom currently pins, regenerate Veil's manifest through Lake, and confirm
mathlib is no longer marked as inherited; without this, Veil's own imports
fail to resolve the moment Loom drops the dependency. Then review its action
semantics, specification monad alias, simplification proofs, logging
instances, and generated quotations, starting from the declarations recorded
in increment A that unfold mathlib's lattice. Reuse its existing candidate
providers rather than routing them through `FinEnum`. Retain its unrelated
mathlib imports during this migration and test coexistence.

Run Veil's configured test library, relevant examples, and extraction
performance suite using the selected Loom revision. Investigate changes in
instance synthesis, normal forms, declaration names, and runtime logs
separately. Do not attribute unrelated baseline failures to the port without
comparison against the recorded revision.

Exit condition: mixed mathlib/Loom consumers work, the documented migration is
accurate, and Veil passes the agreed baseline checks against the new Loom.

**8. Remove the package dependency and verify from clean environments.**

Remove the root `require mathlib` from `lakefile.lean` and regenerate the root
manifest through Lake. Remove unused transitive packages through resolution,
not by manually editing their manifest entries. Keep the separate adapter's
manifest and builds independent. Retain the root library's coverage of all
submodules and its native-library support.

Verify in a new isolated directory with no inherited dependency search path,
pre-existing mathlib package directory, or old Loom build artifacts. Build the
default target and static library. Inspect resolved package dependencies and
the imported environment; neither direct nor indirect mathlib modules may be
present. A source grep alone cannot establish dependency removal.

Build a small external consumer that imports the established extraction entry
point and enables module precompilation. Build another consumer that requires
mathlib plus the integration package. Check Git/package resolution for the
integration's final distribution arrangement, not just a local path build.

Update CI with separate standalone and mathlib-integration jobs. The
standalone job must not populate a mathlib cache. Keep native and genericity
checks in that job. Update the README and migration documentation with actual
imports, package dependencies, and the tested toolchain.

Exit condition: fresh standalone and mixed-consumer builds pass, the package
graph has the intended separation, and measured behavior meets the baseline.

**The tests should target the semantic and integration risks.**

| Area | Cases to cover |
| --- | --- |
| Genericity | Preorder-only specification; non-Boolean complete lattice; Boolean model; dependent function lattices; mixed index/carrier universes and proposition indices |
| Order semantics | Empty bounds; proposition embedding; pointwise operations; complement and implication; indexed monotonicity and congruence |
| Effect composition | Reader/state/exception stacks; both exception interpretations; deterministic laws with their existing nonempty conditions |
| Nondeterminism | Demonic and angelic choice; empty and singleton choices; arbitrary source domains; complete and partial candidate providers |
| Enumeration | Order and duplicate preservation; predicate filtering; custom providers without finite-type machinery |
| Logging and writers | Multiple ordered log entries; logs around divergence and exceptions; result/log component order; arbitrary noncommutative log algebra |
| Extraction | Previously extracted calls; local decidability; ordinary and dependent value lets; zero-, one-, and multiple-argument join points; sequential branching; both `shareValueLets` settings |
| Native execution | Extracted values execute; proof components do not obstruct compilation; representative precompiled downstream module |
| Interoperability | Explicit mathlib conversions; nested predicate instances; no instance loops; core and mathlib syntax coexist |
| Dependencies | Fresh standalone package graph, import graph, and builds contain no mathlib |

Use small fixed executable examples for list/log comparisons and targeted
term-size or sharing checks for extraction. Do not compare exact pretty-printed
proof terms as a substitute for semantic checks. Measure extraction time and
generated-code size against the baseline before setting tolerances; no claimed
speedup follows merely from removing imports.

**The work should be reviewed in coherent increments.**

| Increment | Scope | Depends on |
| --- | --- | --- |
| A | Baseline, reproducible audit, and focused regression fixtures | None |
| A′ | Import trim, targeted regressions, candidate adapter and migration guide, explicit proof repairs, and replacement of `introv` and the meta helpers | A |
| B | Standalone order and control foundations, plus early conversion checks | A |
| C | Monad algebras, effect instances, WP/WLP, and nondeterminism | B |
| D | Candidate boundary, logging/writer migration, and extraction | C |
| E | Complete integration package and Veil migration | D; adapter design begins in B |
| F | Remove root dependency, clean builds, CI, and migration documentation | D and E |

Increment A′ is independently shippable and is the recommended stopping point
if the full removal is deferred.

Keep the existing mathlib requirement during intermediate consumer ports so
reviewable increments can build. New foundation modules should already compile
in a mathlib-free fixture. The final clean build is what rules out hidden
dependencies. Do not maintain two permanent implementations of Loom's
semantics; temporary comparison fixtures should be removed or reduced to
useful regressions after the port.

The largest uncertainty is the order/WLP proof migration and its interaction
with downstream simplification. A rough planning allowance for one developer
familiar with Lean is several working days for baselines and foundations,
roughly one to two weeks for consumer proofs and extraction, and several more
days for interoperability and release checks. Budget approximately two to four
working weeks overall, then revise after increment B. This is an estimate,
not a measured implementation result.

Instance coherence, universe preservation, and definitional equality should
be resolved in the early foundation checks. Extraction sharing and native
execution should be tested as soon as extraction compiles. If either becomes
problematic, narrow the implementation change at that boundary while keeping
the generic API and semantic acceptance criteria intact.
