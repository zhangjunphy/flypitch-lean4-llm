# Flypitch Lean 4

This repository is a Lean 4 port of the upstream Lean 3 Flypitch development:

- upstream source: <https://github.com/flypitch/flypitch>
- target theorem: `independence_of_CH`

The upstream project proves the independence of the continuum hypothesis by combining:

- a first-order logic and completeness development
- Boolean-valued models and forcing
- a ZFC formalization tying both branches together

The current repository is being ported incrementally. The active migration plan and verified
milestones live in `PORT_STATUS.md`.
