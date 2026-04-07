# Flypitch Lean 4 Port Status

This file tracks the actual port sequence and the checks used to verify progress.

## Target

- Upstream repository: `/tmp/flypitch-upstream`
- End goal: port `src/summary.lean` and recover the theorem `independence_of_CH`

## Dependency Split

The upstream project breaks into two large branches that meet in `zfc.lean`.

1. Logic/completeness branch
   - `to_mathlib`
   - `fol`
   - `compactness`
   - `completion`
   - `colimit`
   - `language_extension`
   - `henkin`
   - `completeness`
2. Set-theory/forcing branch
   - `pSet_ordinal`
   - `set_theory`
   - `regular_open_algebra`
   - `cantor_space`
   - `collapse`
   - `bv_tauto`
   - `bvm`
   - `bvm_extras`
   - `bvm_extras2`
   - `aleph_one`
   - `forcing`
   - `forcing_CH`
3. Integration branch
   - `bfol`
   - `zfc`
   - `print_formula`
   - `summary`

## Worker Boundaries

- `Compat.Core`: logic-side subset of upstream `to_mathlib`
- `FOL.Core`: first-order syntax, substitution, proof system
- `FOL.Semantics`: structures, realizations, satisfaction, soundness
- `CompactnessCompletion`: compactness and maximal consistent extensions
- `ColimitLanguageExtension`: directed colimits and language morphisms
- `HenkinCompleteness`: witness extension and completeness theorem
- `PSetOrdinal`: `pSet`/ordinal/cardinal groundwork
- `ForcingTopology`: `set_theory`, `regular_open_algebra`, `cantor_space`
- `Collapse`: collapse poset and Boolean algebra
- `BooleanValuedModels`: `bv_tauto`, `bvm`, `bvm_extras*`, `aleph_one`
- `ForcingResults`: `forcing`, `forcing_CH`
- `ZFCIntegration`: `bfol`, `zfc`, `print_formula`, `summary`

## Milestones

- [x] Normalize the Lean 4 project around a Mathlib-backed `Flypitch` library.
- [x] Record a dependency-ordered port plan grounded in the upstream module graph.
- [x] Port the first shared compat layer in `Flypitch/Compat/Core.lean`.
- [x] Port the initial FOL term syntax layer in `Flypitch/FOL/Syntax.lean`.
- [x] Port FOL formula syntax and structural term/formula operations in `Flypitch/FOL/Formula.lean`.
- [x] Port the basic proof-tree layer and weakening infrastructure in `Flypitch/FOL/Proof.lean`.
- [x] Port the proof-transport lemmas that depend on lift/substitution commutation.
- [x] Extend `Flypitch.FOL` through semantics and soundness.
- [x] Port a small regression target analogous to upstream `abel.lean`.
- [x] Port the front formula-level tranche of `compactness.lean`.
- [ ] Port `pSet_ordinal` as the first forcing-side hard dependency.
- [ ] Port the topology/regular-open/collapse stack.
- [ ] Port Boolean-valued models.
- [ ] Reconnect both branches in `zfc`.
- [ ] Re-establish `independence_of_CH`.

## Verification Policy

Every completed milestone must satisfy both checks:

1. `lake build`
2. A concrete imported module corresponding to the milestone compiles cleanly without `axiom` placeholders.

## Current Verified Surface

- `Flypitch/Compat/Core.lean`
- `Flypitch/FOL/Syntax.lean`
- `Flypitch/FOL/Formula.lean`
- `Flypitch/FOL/Proof.lean`
- `Flypitch/FOL/Semantics.lean`
- `Flypitch/Compactness.lean`
- `Flypitch/Examples/Abel.lean`

## Next Blocker

The next critical blocker is the remaining theory-level half of upstream `compactness.lean` and the
start of `completion.lean`. The newly ported `Flypitch/Compactness.lean` covers only the generic
utilities and formula-level `proof_compactness`; the rest is blocked on sentence/theory
infrastructure that still lives later in upstream `fol.lean`.

The next Lean 4 tranche is:

- sentence/theory infrastructure from upstream `fol.lean`
- theory-level compactness/model-existence infrastructure
- completion and maximal-consistent-extension machinery

After that, the next dependency chain is `completion.lean`, `colimit.lean`, `language_extension.lean`,
`henkin.lean`, and `completeness.lean`. The forcing branch still starts later at `pSet_ordinal.lean`.
