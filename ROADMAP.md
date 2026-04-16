# Backward Roadmap to Coste 3.2

Detailed planning document for the first real proof milestone in this repository:
Coste's Curve Selection Lemma (Theorem 3.2).

This roadmap is intentionally backward from the target. The goal is to make the
implementation order decision-complete before more Lean code is written.

## Summary

- Target milestone: a genuine proof of Coste 3.2 over the current abstract
  `OMinStructure` interface on `ℝ^n`.
- Stop at the first proved version of `curveSelection`; do not yet plan the
  rest of Chapter 3.
- Follow Coste's proof path, not a different optimized route.
- Work abstractly first; postpone the concrete semialgebraic/o-minimal
  instance over `ℝ`.

## Current Boundary

The current library already fixes the raw geometric interface:

- `Rn`
- `DefinableSetOf`, `DefinableMapOf`
- `CellShape`, `CellOf`, `CdcdOf`
- `SplitCellOf`, `SplitCdcdOf`

The following fields in `OMinStructure` are temporary placeholders and must be
retired in this order:

1. `monotonicity_axiom`
2. `oneVarEventuallyContinuous_axiom`
3. `uniformFiniteness_axiom`
4. `cellDecomposition_axiom`
5. `piecewiseContinuity_axiom`
6. `definableChoice_axiom`
7. `curveSelection_axiom`

The exported theorem names stay fixed throughout:

- `monotonicity`
- `uniformFiniteness`
- `cellDecomposition`
- `piecewiseContinuity`
- `definableChoice`
- `curveSelection`

## Layer 1: High-Level Dependency Graph

Read the dependency graph from the target backward.

1. **Theorem 3.2: Curve Selection**
   - depends on `Theorem 3.1 Definable Choice`
   - depends on one-variable eventual continuity near an endpoint
   - uses only primitive metric-set definability on top of the current Chapter 1 interface

2. **Theorem 3.1: Definable Choice**
   - depends on the split form of `Theorem 2.10 Cell Decomposition`
   - uses explicit cellwise selectors for graph, bounded band, and half-infinite band cases

3. **One-variable eventual continuity**
   - depends on `Theorem 2.1 Monotonicity`
   - is first proved for scalar-valued functions, then lifted coordinatewise to `Rn`

4. **Theorem 2.1: Monotonicity**
   - depends on `Lemma 2.2`
   - depends on one-dimensional o-minimal helper lemmas about intervals, finite fibers, and monotone bijections

5. **Chapter 2 induction package**
   - `Theorem 2.9 Uniform Finiteness`
   - `Theorem 2.10 Cell Decomposition`
   - `Theorem 2.12 Piecewise Continuity`
   - these are proved simultaneously by induction on dimension, exactly as Coste does

6. **Cell preliminaries needed by the Chapter 2 package**
   - `Definition 2.4` cdcd data and graph/band recursion
   - `Proposition 2.5` cell homeomorphism to `R^d`
   - `Exercise 2.6` open/full-dimensional cells and density of full-dimensional cells
   - `Exercise 2.8` definable connectedness of cells

7. **Minimal Chapter 1 primitives**
   - boolean closure and projection closure
   - definable intervals in `ℝ`
   - definable constants and affine maps
   - definable open balls and metric tubes
   - no concrete semialgebraic instance yet

## Layer 2: Fine-Grained Theorem Breakdown

### Stage A: Cell Preliminaries and Structural API

#### Coste 2.4: cdcd

- **Lean target**
  - Keep `CellShape`, `CellOf`, `CdcdOf`, `SplitCellOf`, and `SplitCdcdOf`.
  - Add future constructor-level lemmas for one-dimensional cells, graph cells,
    bounded bands, lower-unbounded bands, and upper-unbounded bands.
- **Needed because**
  - later proofs need to case-split on cells and expose the section functions
    directly instead of unpacking existential descriptions.
- **Hidden Lean lemmas to formalize**
  - projection of a graph cell is its base cell
  - projection of a band cell is its base cell
  - graph and band carriers are definable from definable section functions
  - split cells have pairwise disjoint domains when their cores are disjoint
- **Current interface interaction**
  - this stage stabilizes the use of `CellOf` and `SplitCdcdOf` as the internal
    workhorse for Chapter 2 and Chapter 3
- **Axiom retired**
  - none directly; this stage supports later retirement

#### Coste 2.5: cell homeomorphism

- **Lean target**
  - Prove constructor lemmas yielding the stored `CellOf.homeomorph` data in a
    uniform way.
  - Keep the exported wrapper `cellHomeomorph`.
- **Proof skeleton**
  - graph case: reuse the base-cell homeomorphism
  - band case: map to `R^d × R` and then to `R^(d+1)` using the explicit
    rational transformation in Coste
- **Hidden Lean lemmas**
  - continuity and inverse continuity of the band parameterization
  - handling bounded and half-infinite bands as separate formulas rather than
    encoding omitted denominators ad hoc
- **Current interface interaction**
  - this stage feeds lower-dimensional reductions in `UF_n` and `PC_n`
- **Axiom retired**
  - none directly

#### Coste 2.6 and 2.8: openness, density, and connectedness of cells

- **Lean targets**
  - a cell is open iff its dimension equals ambient dimension
  - the union of full-dimensional cells is dense
  - every cell is definably connected
- **Proof role**
  - open/full-dimensional density is used in `PC_n`
  - definable connectedness of cells is used in the third step of `UF_n`
- **Hidden Lean lemmas**
  - every open box meets a full-dimensional cell
  - boxes and affine spaces are definably connected
  - definable connectedness is preserved by definable homeomorphism
- **Axiom retired**
  - none directly

### Stage B: One-Variable Package

#### Coste 2.2: key lemma for one-variable definable functions

- **Lean target**
  - For `f : (a,b) → ℝ` definable, prove there is a subinterval on which `f` is
    constant or strictly monotone and continuous.
- **Proof skeleton**
  1. If no subinterval is constant, every fiber `f⁻¹(y)` is finite.
  2. The image `f '' I` is infinite, hence contains an interval `J`.
  3. Define `g(y) = min (f⁻¹(y))`, prove it is definable, and obtain a
     subinterval where `f` is injective.
  4. Partition the interval into the four local sign-pattern sets
     `Φ+,+`, `Φ+,-`, `Φ-,+`, `Φ-,-`.
  5. Show `Φ+,+` and `Φ-,-` are finite by the contradiction argument through
     `Ψ+,-` and `Ψ-,+`.
  6. Shrink to an interval where `f` is strictly increasing or strictly
     decreasing.
  7. Shrink once more to a strictly monotone bijection between intervals and
     conclude continuity.
- **Hidden Lean lemmas**
  - infinite definable subsets of `ℝ` contain an interval
  - definable image of a definable interval under a definable map
  - finite-fiber minimum selection on `ℝ`
  - interval preimage/image lemmas for injective definable maps
  - continuity of a strictly monotone bijection between intervals
  - least upper bound / greatest lower bound arguments in interval form
- **Current interface interaction**
  - uses only `DefinableMapOf`, interval definability, projection closure, and
    one-dimensional o-minimality
- **Axiom retired**
  - prerequisite for `monotonicity_axiom`

#### Coste 2.1: Monotonicity Theorem

- **Lean target**
  - For definable `f : (a,b) → ℝ`, produce a finite subdivision on which `f` is
    continuous and either constant or strictly monotone.
- **Proof skeleton**
  - define the local behavior sets `X=`, `X↑`, `X↓`
  - show the complement is finite by applying Lemma 2.2 to any interval in the
    complement
  - pass from the finite complement to a finite subdivision
  - on each resulting interval, use the least-upper-bound argument to upgrade
    local behavior to global behavior
- **Hidden Lean lemmas**
  - finite definable subsets of `ℝ` admit a canonical ordered enumeration
  - removing a finite set from an interval yields finitely many subintervals
- **Current interface interaction**
  - proves the exported theorem `monotonicity`
- **Axiom retired**
  - `monotonicity_axiom`

#### Coste 2.3 plus Chapter 3 input: endpoint limits and vector eventual continuity

- **Lean targets**
  - scalar definable functions on `(a,b)` have one-sided limits in
    `ℝ ∪ {±∞}`
  - for definable `f : (a,∞) → Rn`, there exists `ε > 0` such that `f` is
    continuous on `(a, a+ε)`
- **Proof skeleton**
  - derive one-sided scalar limits from monotonicity on a final subinterval
  - for vector-valued maps, apply the scalar result coordinatewise and take the
    minimum witness interval
- **Hidden Lean lemmas**
  - coordinatewise continuity criterion for maps into `Fin n → ℝ`
  - taking the minimum of finitely many positive radii
- **Current interface interaction**
  - proves the exported eventual continuity theorem used later in 3.2
- **Axiom retired**
  - `oneVarEventuallyContinuous_axiom`

### Stage C: Chapter 2 Simultaneous Induction

This stage must be treated as one bundle. The proof order inside dimension `n`
is exactly Coste's:

1. prove `UF_n`
2. prove `CDCD_n`
3. prove `PC_n`

Base case `n = 1`:

- `UF_1` is trivial
- `CDCD_1` comes from o-minimality on `ℝ`
- `PC_1` is a direct consequence of monotonicity

Induction step assumes `UF_m`, `CDCD_m`, and `PC_m` for every `m < n`.

#### Coste 2.9: Uniform Finiteness

- **Lean target**
  - For definable `A ⊆ R^(n-1) × R` with finite fibers, prove a uniform bound
    on fiber cardinalities.
- **Proof skeleton**
  1. Normalize fibers into `(-1,1)` using an explicit semialgebraic
     homeomorphism.
  2. Define the ordered fiber functions `f_i`.
  3. Define good, bad, and normal points.
  4. Prove the set of good points is definable.
  5. Prove the set of good points is dense using `PC_{n-1}`.
  6. Adapt a `cdcd` of `R^(n-1)` to the good set using `CDCD_{n-1}`.
  7. On full-dimensional cells, prove fiber cardinality is locally constant and
     hence constant by definable connectedness.
  8. On lower-dimensional cells, pull back along `θ_D : D ≃ R^d` and invoke
     `UF_d`.
- **Hidden Lean lemmas**
  - definability of the ordered fiber functions `f_i`
  - definability of `good`, `bad`, and `normal`
  - continuity of lim-inf style definable constructions when `PC_{n-1}` is available
  - graph containment/disjointness arguments for `β`, `β^-`, `β^+`
  - transport of finite-fiber cardinality bounds across `θ_D`
- **Current interface interaction**
  - this stage depends critically on `CellOf.homeomorph` and cell connectedness
- **Axiom retired**
  - `uniformFiniteness_axiom`

#### Coste 2.10: Cell Decomposition

- **Lean target**
  - For finitely many definable subsets of `R^n`, produce a split cdcd adapted
    to them.
- **Proof skeleton**
  1. Define the boundary set in `R^(n-1) × R`.
  2. Apply `UF_n` to get finitely many ordered boundary graphs `f_i`.
  3. Define the finite type of a base point by graph membership and band membership.
  4. Use `CDCD_{n-1}` to partition `R^(n-1)` by type.
  5. Use `PC_{n-1}` so each boundary function is either nowhere defined or
     continuous on each base cell.
  6. Build the split cdcd in `R^n`.
  7. Equip each split cell with its selector:
     - graph cell: section itself
     - bounded band: midpoint
     - lower-unbounded band: upper section minus `1`
     - upper-unbounded band: lower section plus `1`
- **Hidden Lean lemmas**
  - boundary fibers are finite
  - type equality is definable and constant on cells
  - selector formulas are definable and land in the target cell
  - pairwise disjointness passes from cores to domains
- **Current interface interaction**
  - this stage intentionally returns `SplitCdcdOf`, not only `CdcdOf`, so local
    choice data are constructed here and reused in Chapter 3
- **Axiom retired**
  - `cellDecomposition_axiom`

#### Coste 2.12: Piecewise Continuity

- **Lean target**
  - For definable `f : A → ℝ`, produce a cdcd adapted to `A` such that `f`
    is continuous on each cell contained in `A`.
- **Proof skeleton**
  1. First handle an open box `B × (a,b)`.
  2. For each `x`, define `λ(x)` as the endpoint of the largest initial interval
     of monotone continuity in the last coordinate.
  3. Use monotonicity and `PC_{n-1}` to shrink to a smaller open box where
     every fiber `f(x,·)` is continuous and monotone.
  4. Let `C` be the set of points where `f(·,y)` is continuous in the base
     variable.
  5. Use `PC_{n-1}` and `CDCD_n` to show `C` contains an open subbox.
  6. Deduce continuity on that subbox from continuity in each variable plus
     monotonicity in the last variable.
  7. For general `A`, use `CDCD_n` adapted to the continuity locus and reduce
     lower-dimensional cells along `θ_F : F ≃ R^d`.
- **Hidden Lean lemmas**
  - definability of `λ`
  - open-box continuity criterion from monotone slices
  - density of the continuity-in-base-variable locus
  - transport of piecewise continuity across cell homeomorphisms
- **Current interface interaction**
  - uses `cellHomeomorph` and the full-dimensional cell facts from Stage A
- **Axiom retired**
  - `piecewiseContinuity_axiom`

### Stage D: Chapter 3 up to Curve Selection

#### Coste 3.1: Definable Choice

- **Lean target**
  - For definable `A ⊆ R^m × R^n`, prove the existence of a definable
    selector on `prefixProjection m n A`.
- **Proof skeleton**
  1. Reduce from general `n` to `n = 1` by iterated projection.
  2. Apply the split version of `CDCD_(m+1)` adapted to `A`.
  3. On each split cell, use the selector already built at the cell level.
  4. Glue the cellwise selectors using pairwise disjoint domains and
     `definable_piecewise`.
- **Hidden Lean lemmas**
  - iterated-choice composition from `n = 1` to general `n`
  - domainwise disjointness for split cells
  - global gluing of finitely many definable selectors over a finite partition
- **Current interface interaction**
  - the theorem should become a short wrapper over the split cdcd returned by
    cell decomposition, not a large standalone proof
- **Axiom retired**
  - `definableChoice_axiom`

#### Coste 3.2: Curve Selection

- **Lean target**
  - For definable `A ⊆ R^n` and `b ∈ closure A`, produce a definable continuous
    `γ : [0,1) → R^n` with `γ(0) = b` and `γ((0,1)) ⊆ A`.
- **Proof skeleton**
  1. Define `X = {(t, x) | x ∈ A ∧ ‖x - b‖ < t}`.
  2. Prove `prefixProjection 1 n X = Ioi 0`.
  3. Apply `definableChoice` to obtain `δ : (0,∞) → A` with
     `‖δ(t) - b‖ < t`.
  4. Apply one-variable eventual continuity to shrink to `(0, ε)`.
  5. Use the metric bound to extend continuously at `0` with value `b`.
  6. Rescale by `t ↦ ε t` to obtain a map on `[0,1)`.
- **Hidden Lean lemmas**
  - definability of `X` from `definable_metricTube`
  - the projection of `X` is exactly `Ioi 0` using the closure hypothesis
  - the metric estimate implies `δ(t) → b` as `t → 0+`
  - rescaling preserves definability and continuity on `Ico (0:ℝ) 1`
- **Current interface interaction**
  - this stage only uses earlier proved material plus existing primitive
    ball/tube definability
- **Axiom retired**
  - `curveSelection_axiom`

## Future Module Layout

When Lean development resumes, split the current monolithic milestone work into
chapter-oriented modules:

- `LeanOMIN/Chapter2/Cells.lean`
- `LeanOMIN/Chapter2/Monotonicity.lean`
- `LeanOMIN/Chapter2/Induction.lean`
- `LeanOMIN/Chapter3/Choice.lean`
- `LeanOMIN/Chapter3/CurveSelection.lean`

`LeanOMIN/Ominimal.lean` should remain the public interface and re-export
surface. As proofs land, it should stop storing theorem-shaped `_axiom` fields
and instead import the new chapter modules and expose the proved theorems under
the same names.

## Acceptance Criteria

The roadmap is complete only if all of the following hold:

- every step from `curveSelection` back to the primitive definability interface
  is named and ordered;
- every numbered Coste result on the path to 3.2 is listed;
- every current theorem-shaped `_axiom` field is assigned a retirement stage;
- the proof order is fixed;
- the abstraction boundary is fixed;
- the stopping point is fixed;
- the hidden Lean-side intermediate lemmas that Coste omits are made explicit.

## Immediate Next Action

Do not write new Lean code yet. The next work item after accepting this
document is to expand the one-variable stage into a result-by-result checklist,
starting with the hidden lemmas needed for Coste 2.2.
