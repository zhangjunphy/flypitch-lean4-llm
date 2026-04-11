# Blueprint Writing Plan

This file records how the blueprint should be written and how the current pass
rewrites it. The immediate goal of this pass is to shift the blueprint away
from a Lean-centric description of declarations and toward a mathematical
account of the constructions and theorems formalized in the repository.

The model is the style used in the FLT blueprint at
`ImperialCollegeLondon/FLT`: the reader should first encounter the mathematics,
the purpose of each construction, and the logical dependence between chapters.
Formalization details should support that story rather than drive it.

## Writing Rules

- Write in mathematical language first. State the definition, theorem, or
  construction as mathematics before naming Lean declarations.
- Keep Lean identifiers secondary. Mention file names and declaration names only
  to orient a reader who wants to inspect the formalization.
- Organize each chapter around a mathematical goal, not around the order of
  declarations in the code.
- Explain why each construction is introduced and how it is used later.
- Prefer ordinary mathematical sentences over long lists of API names.
- Mention implementation boundaries explicitly, but do so as project status,
  not as the main content of a chapter.
- Keep the exposition faithful to the current Lean 4 code. Do not describe
  unported results as if they were already formalized.

## Chapter Template

Each substantial chapter should follow the same pattern.

1. Start with a short paragraph saying what mathematical problem the chapter
   solves.
2. Introduce the main objects in standard mathematical language.
3. State the central propositions and explain the argument at the level a
   mathematician would expect in a blueprint.
4. Only after the mathematics is clear, point to the main Lean files or key
   declarations that realize it.
5. End by explaining how the chapter feeds into the next one.

In particular, avoid paragraphs whose main subject is a Lean constant such as
`foo_bar_baz`. If a declaration name is worth mentioning, it should usually
appear near the end of a paragraph or in a short supporting sentence.

## Scope For This Pass

This pass covers the currently implemented logic-side blueprint:

1. `Overview`
2. `First-Order Logic Core`
3. `Compactness And Completion`
4. `Colimits And Language Extensions`
5. `Henkinization`
6. `Status And Next Frontier`

The forcing and ZFC side remains out of scope except for brief status remarks.

## Concrete Rewrite Goals

### Overview

- Present the project as a mathematical program first.
- Explain the current Lean 4 boundary without making the chapter read like a
  repository inventory.
- Give a reader-oriented roadmap through the logic-side argument.

### First-Order Logic Core

- Describe languages, syntax, derivability, semantics, and theories in ordinary
  first-order logic terminology.
- Keep the explanation of de Bruijn syntax brief and motivated.
- Treat Lean structures and notation as implementation notes rather than as the
  main narrative.

### Compactness And Completion

- Present compactness as the finitary principle behind later consistency
  arguments.
- Present completion as the maximal-consistent-extension argument, with Zorn's
  lemma appearing as part of the mathematics rather than as a code artifact.

### Colimits And Language Extensions

- Emphasize the mathematical role of directed colimits, language maps,
  reducts, and reflection.
- Treat symbol-support lemmas and fresh-constant arguments as part of the
  witness machinery, not as isolated implementation tricks.

### Henkinization

- Present the chapter as the construction of a Henkin language and a consistent
  Henkin extension.
- Keep the infinite-language and finite-stage comparison story mathematical.
- State clearly that the current repository reaches complete Henkin extensions
  but not the final completeness theorem for arbitrary theories.

### Status And Next Frontier

- Summarize the verified mathematical output of the present port.
- State the current project boundary cleanly and briefly.
- Avoid repeating long lists of Lean module names unless they serve a specific
  documentary purpose.

## Revision Sequence

1. Rewrite `blueprint/PLAN.md` to establish the documentation policy.
2. Rewrite each chapter so the mathematics leads and Lean details follow.
3. Do a coherence pass to make the chapter transitions read as a single
   mathematical story.
4. Rebuild or otherwise check the blueprint source for obvious formatting
   issues.

## Acceptance Criteria

- A mathematician can read the blueprint without needing to know Lean naming
  conventions.
- The main dependency chain is clear: first-order logic, compactness and
  completion, language extension, henkinization.
- Lean identifiers still appear when helpful, but they no longer dominate the
  exposition.
- The rewritten text remains accurate with respect to the current Lean 4
  development.
