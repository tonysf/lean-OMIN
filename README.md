# LeanOMIN

Lean 4 formalization of Michel Coste's lecture notes on o-minimal geometry.

## Scope

This repository is building a reusable Lean development around definable sets,
definable maps, and the basic infrastructure of o-minimal geometry over the
reals. The immediate milestone is Coste 3.2, the Curve Selection Lemma over
`ℝ^n`.

The project is library-first rather than a list of isolated theorem statements.
The goal is to formalize the supporting layer needed for later chapters as
well: coordinates on `ℝ^n`, graph-based definability, one-variable
regularity results, cell-style decomposition infrastructure, definable choice,
and curve selection.

Where Coste's exposition does not line up exactly with current Mathlib APIs,
the formalization follows the Lean/Mathlib statement that is mathematically
correct in context.

## Current Status

- `lake build` passes.
- `LeanOMIN/` is currently `sorry`-free.
- The project currently includes:
  - `Rn n := Fin n → ℝ` as the ambient model for `ℝ^n`;
  - coordinate encodings and graph-based predicates for definable sets and
    maps;
  - an abstract `OMinStructure` interface packaging the closure properties and
    milestone theorems used by the current development;
  - recursive cell-shape data, cylindrical decomposition scaffolding, and
    sanity-check examples for affine maps, halfspaces, open balls, definable
    choice, and curve selection.
- Current frontier:
  - the public interfaces for monotonicity, uniform finiteness, cell
    decomposition, piecewise continuity, definable choice, and curve selection
    are in place;
  - the remaining core work is to replace the current abstract Chapter 2 and
    Chapter 3 axioms with actual proofs inside the library, and then build a
    concrete semialgebraic/o-minimal instance over `ℝ`.

## Roadmap

The detailed backward proof roadmap to Coste 3.2 lives in
[`ROADMAP.md`](ROADMAP.md).

1. Prove the one-variable and cell-decomposition layer from Coste Chapter 2
   inside Lean, rather than leaving it axiomatic.
2. Derive Definable Choice (Coste 3.1) and Curve Selection (Coste 3.2) from
   that infrastructure.
3. Add a concrete semialgebraic or o-minimal instance over `ℝ`.
4. Continue formalizing the later parts of the notes chapter-by-chapter once
   the curve-selection milestone is genuinely proved.

## Repository Layout

- `LeanOMIN.lean`: top-level import for the current formalization.
- `LeanOMIN/Basic.lean`: coordinates, encodings, products, graphs, and
  projection helpers.
- `LeanOMIN/Ominimal.lean`: abstract o-minimal interface, cell/decomposition
  scaffolding, and exported milestone theorem statements.
- `LeanOMIN/Examples.lean`: sanity-check examples against the current
  interface.
- `OMIN.pdf`: local reference copy of Coste's lecture notes.

## Building

```bash
lake build
```

The required Lean toolchain is pinned in `lean-toolchain`.
