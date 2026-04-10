# Flypitch Lean 4 Port Status

This file tracks the actual port sequence and the checks used to verify progress.

## Target

- Upstream repository: `https://github.com/flypitch/flypitch`
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
- [x] Port sentence/theory infrastructure from upstream `fol.lean` in `Flypitch/FOL/Theory.lean`.
- [x] Finish the theory-level compactness lemmas in `Flypitch/Compactness.lean`.
- [x] Port maximal consistent extension machinery from upstream `completion.lean` in `Flypitch/Completion.lean`.
- [x] Port the directed-colimit and language-extension layer in `Flypitch/Colimit.lean` and `Flypitch/LanguageExtension.lean`.
- [x] Port the early Henkin language-colimit slice in `Flypitch/Henkin.lean`.
- [x] Port Henkin term/formula/bounded-formula chains and comparison maps into `LInfty`.
- [x] Prove bijectivity of the term/formula comparison maps into `LInfty`.
- [x] Port bounded-term/bounded-formula comparison bijectivity and the induced equivalence at bounded formulas.
- [x] Port Henkin witness properties, `witInfty`, the raw `ι`/`T_infty` theory-chain scaffolding, and the enough-constants proof for `henkinization`.
- [x] Port the fresh-constant generalization layer in `Flypitch/LanguageExtension.lean` (`boundedFormulaSubstSentence`, `generalize_constant`, `sgeneralize_constant`).
- [ ] Prove consistency of the Henkin theory step and `ι`-chain, then finish the henkinization/completed-theory bridge.
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
- `Flypitch/FOL/Theory.lean`
- `Flypitch/Compactness.lean`
- `Flypitch/Completion.lean`
- `Flypitch/Colimit.lean`
- `Flypitch/LanguageExtension.lean`
- `Flypitch/Henkin.lean`
- `Flypitch/Examples/Abel.lean`

## Next Blocker

The next critical blocker is still the remaining theory-level half of upstream `henkin.lean`,
but the frontier has moved forward again. The repository now has the directed-colimit,
language-extension, Henkin language-chain infrastructure, the induced comparison maps into
`LInfty`, bijectivity for term/formula/bounded-term/bounded-formula comparison maps, and the
bounded-formula equivalence needed to choose representatives. It also now has the witness
property definition, the extracted `witInfty` representative, the recursive Henkin theory step,
the raw `ι` chain inside `Theory (LInfty L)`, the induced inclusion lemmas along that chain,
the `T_infty` union theory definition, the local enough-constants interface, and the proof that
the raw `henkinization` already has enough constants. On the logic-support side,
`LanguageExtension.lean` now also has the missing reflection infrastructure: image-theory
formula bookkeeping, reflection commuting with lift/substitution, proof reflection
(`reflect_prf_gen` / `reflect_prf` / `reflect_sprf`), and consistency preservation for
induced theories.

What is still missing is now the Henkin-specific consistency side on top of the freshly ported
generalization layer. The repository has the reusable fresh-constant package in
`LanguageExtension.lean` (`boundedFormulaSubstSentence`, `generalize_constant`,
`sgeneralize_constant`), but it still needs the one-step consistency proof for the Henkin theory
step, reflection of inconsistency back along the `ι` embeddings, packaging the chain as a
consistent directed union, and finally the bridge from `henkinization` to a completed Henkin
theory.

The next Lean 4 tranche is:

- `henkin.lean`
- `completeness.lean`

After that, the remaining logic/completeness dependency chain is the rest of `henkin.lean` followed by
`completeness.lean`. The forcing branch still starts later at `pSet_ordinal.lean`.
