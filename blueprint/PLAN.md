# Blueprint Writing Plan

This file tracks the documentation plan for the Lean 4 blueprint. The goal is to document
the currently implemented part of the project in a way that is mathematically readable,
faithful to the Lean code, and easy to extend as more of the port lands.

## Scope Rules

- Document only material that is already implemented in the Lean 4 repository.
- Keep the mathematics ahead of the code details: explain the construction first, then name
  the Lean declarations that realize it.
- Treat the logic/completeness branch as the current documented surface.
- Mention the forcing and ZFC branches only to explain project context, not as completed content.
- Prefer one coherent chapter per module cluster instead of a long single overview page.

## Planned Chapter Structure

1. `Overview`
   - Project goal and current port boundary
   - Dependency split between the logic branch and the forcing branch
   - Reading guide for the implemented material
2. `First-Order Logic Core`
   - Languages, terms, formulas, and de Bruijn substitution
   - Natural deduction proof system
   - Structures, realization, satisfaction, and soundness
   - Sentences, theories, bounded syntax, and the abelian-group sanity check
3. `Compactness And Completion`
   - Proof compactness
   - Theory compactness
   - Consistency-preserving unions
   - Maximal consistent extensions and completeness of a maximal extension
4. `Colimits And Language Extensions`
   - Directed diagrams and colimits
   - Language morphisms and reducts
   - Symbol filtering and reflection lemmas
   - The fresh-constant generalization package
5. `Henkinization`
   - The language chain and the colimit language `LInfty`
   - Comparison maps for terms and formulas
   - Enough constants and witness sentences
   - The step theory, the `iota` chain, `TInfty`, and consistency preservation
   - Completion of the Henkinization to a complete Henkin theory
6. `Status And Next Frontier`
   - What is now documented
   - What remains unported
   - Where the forcing-side documentation should begin once `pSet_ordinal` lands

## Iteration Order

### Iteration 1

- Write `Overview`
- Write `First-Order Logic Core`
- Keep the exposition self-contained enough that a new reader can understand later chapters

Status: completed

### Iteration 2

- Write `Compactness And Completion`
- Add links back to the theory-level notions introduced in Iteration 1

Status: completed

### Iteration 3

- Write `Colimits And Language Extensions`
- Explain why language extension machinery is needed before Henkinization

Status: completed

### Iteration 4

- Write `Henkinization`
- Focus on the actual implemented chain rather than the eventual completeness theorem statement

Status: completed

### Iteration 5

- Write `Status And Next Frontier`
- Do a coherence pass across the blueprint
- Tighten terminology and remove duplicated explanations

Status: completed

## Acceptance Criteria For Each Iteration

- The chapter is consistent with current Lean 4 declarations.
- The chapter clearly distinguishes what is implemented from what is still planned.
- The exposition explains the mathematical purpose of the main constructions, not just their names.
- The blueprint source remains organized into small chapter files.

## Second Pass Plan

The first pass established chapter coverage for the currently implemented
content. The second pass improves navigation, coherence, and reader guidance.

### Second Pass Iteration 1

- Add chapter labels and explicit cross-references between chapters
- Add a roadmap section so the blueprint reads as a single argument rather than
  disconnected summaries

Status: completed

### Second Pass Iteration 2

- Tighten the overview and frontier chapters so they point more clearly to the
  current mathematical dependency chain
- Reduce repetition where the same declarations are reintroduced in multiple
  places

Status: completed

### Second Pass Iteration 3

- Add a final coherence pass aimed at web readability
- Rebuild the blueprint and fix any new layout problems introduced by the
  navigation improvements

Status: completed
