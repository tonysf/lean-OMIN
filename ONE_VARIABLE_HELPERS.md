# One-Variable Helper Inventory

Symbol-level planning document for the helper lemma stack behind the
one-variable package in `ONE_VARIABLE_CHECKLIST.md`.

This document expands only tasks `T1` through `T3`:

- interval helper layer
- finite-fiber choice on `ℝ`
- injective interval-map layer

It is still a planning document, not an implementation file. The purpose is to
fix the helper granularity so the future Lean implementation of Coste 2.2 does
not need to make fresh architectural decisions.

## Summary

- Target future module: `LeanOMIN/Chapter2/Monotonicity.lean`
- Scope: internal helper lemmas only
- Consumers:
  - Coste 2.2
  - Coste 2.1
  - Exercise 2.3
  - vector eventual continuity near an endpoint

These lemmas are internal by default. They should not be re-exported from
`LeanOMIN.lean` unless later chapters genuinely depend on them.

## Naming Policy

The names below are intended as the canonical targets unless Mathlib naming
pressure forces a small adjustment.

Rules:

- prefer descriptive names over theorem-number names
- keep interval domain/codomain information in the name when it matters
- reserve public names for the exported theorems already fixed in
  `Ominimal.lean`

## Group H1: Interval Structure Helpers

These are the first lemmas to implement. They should avoid definability when
possible and live as plain order/topology facts over `ℝ`; only the final
"infinite definable set contains interval" results need the o-minimal
interface.

### H1.1 Local interval extraction

- `exists_Ioo_subset_of_mem_Ioo`
  - **Intent**: if `x ∈ Ioo a b`, produce `u v` with
    `x ∈ Ioo u v` and `Ioo u v ⊆ Ioo a b`
  - **Role**: lets later proofs pass from pointwise local statements to actual
    open subintervals

- `exists_small_Ioo_around_mem_Ioo`
  - **Intent**: metric-style version of interval shrinking around a point in an
    open interval
  - **Role**: supports epsilon neighborhood statements in the local pattern
    predicates `Φ` and `Ψ`

### H1.2 Finite sets and subdivisions on `ℝ`

- `Finite.subset_interval_has_min`
  - **Intent**: a nonempty finite subset of a bounded-below interval has a
    minimum
  - **Role**: supports minimum fiber selection

- `Finite.subset_interval_has_max`
  - **Intent**: a nonempty finite subset of a bounded-above interval has a
    maximum
  - **Role**: used in the `Φ+,+`/`Φ-,-` contradiction step

- `exists_strictMono_embedding_of_finite_real_set`
  - **Intent**: package a finite subset of `ℝ` as an ordered list / finite
    chain
  - **Role**: supports conversion from finite bad sets to subdivisions

- `exists_subdivision_cover_compl_finite`
  - **Intent**: for finite `F ⊆ Ioo a b`, produce an ordered finite sequence of
    breakpoints whose open gaps are exactly the connected components of
    `Ioo a b \ F`
  - **Role**: supports the final step of Coste 2.1

### H1.3 O-minimal one-dimensional interval extraction

- `definable_infinite_subset_real_contains_Ioo`
  - **Intent**: if `S : Set ℝ` is definable and infinite, then there exist
    `u < v` with `Ioo u v ⊆ S`
  - **Role**: used twice in Coste 2.2:
    - once on `f '' I`
    - once on the sets where a local pattern holds

- `definable_subset_real_finite_or_contains_Ioo`
  - **Intent**: packaged dichotomy form of one-dimensional o-minimality
  - **Role**: more convenient front-end for proofs by contradiction

- `definable_partition_interval_one_piece_contains_subinterval`
  - **Intent**: if a definable interval is partitioned into finitely many
    definable pieces and one piece is infinite, that piece contains a
    subinterval
  - **Role**: useful in the `Φ` partition and later in monotonicity

## Group H2: Finite-Fiber Choice on `ℝ`

These lemmas formalize Coste's first-step selector `g(y) = min(f⁻¹(y))`.

### H2.1 Fiber finiteness from non-constancy

- `fiber_finite_of_no_const_subinterval`
  - **Intent**: if `f : Ioo a b → ℝ` is definable and not constant on any open
    subinterval, then every fiber is finite
  - **Role**: first sentence of Coste 2.2

- `image_infinite_of_no_const_subinterval`
  - **Intent**: under the same hypotheses, `Set.range f` is infinite
  - **Role**: feeds `definable_infinite_subset_real_contains_Ioo`

### H2.2 Minimum selector on finite fibers

- `fiberMinDomain`
  - **Intent**: a private definition for the set of `y` with nonempty fiber
  - **Role**: gives a named domain for the selector

- `fiberMin`
  - **Intent**: a private noncomputable selector `y ↦ min {x | f x = y}`
  - **Role**: the actual Coste selector

- `fiberMin_mem`
  - **Intent**: if `y` lies in the selector domain, then `fiberMin y` lies in
    the domain interval and satisfies `f (fiberMin y) = y`
  - **Role**: turns the selector into a right inverse

- `definable_fiberMin`
  - **Intent**: `fiberMin` is definable on its selector domain
  - **Role**: required before applying one-dimensional interval extraction to
    the image of `fiberMin`

### H2.3 Right-inverse consequences

- `injective_of_leftInverse_on`
  - **Intent**: standard helper turning `g ∘ f = id` on a set into
    injectivity of `f` there
  - **Role**: used after shrinking to the image of `fiberMin`

- `range_infinite_of_injective_definable_on_interval`
  - **Intent**: the image of an injective definable interval map is infinite
  - **Role**: ensures the selector image contains a subinterval

- `exists_injectiveOn_Ioo_of_no_const_subinterval`
  - **Intent**: package the whole first step of Coste 2.2 as a reusable lemma
  - **Role**: clean handoff from H2 into the local-pattern stage

## Group H3: Injective Interval Maps

These lemmas prepare the second and third steps of Coste 2.2.

### H3.1 Local pattern predicates

- `LocPattern`
  - **Intent**: an internal inductive or definitional wrapper for
    `Φ+,+`, `Φ+,-`, `Φ-,+`, `Φ-,-`
  - **Role**: avoids carrying four raw formulas everywhere

- `locPattern_definable`
  - **Intent**: each pattern set is definable
  - **Role**: required for interval-extraction arguments

- `locPattern_partition`
  - **Intent**: on an injective interval, every point lies in exactly one local
    pattern
  - **Role**: sets up the finiteness contradiction

### H3.2 Contradiction mechanics for `Φ+,+` and `Φ-,-`

- `exists_PsiPlusMinus_of_not_eventually_up`
  - **Intent**: package the passage from the failure of eventual global
    increase to a `Ψ+,-` witness
  - **Role**: collapses the densest part of Coste's argument into a named lemma

- `finite_locPattern_pp`
  - **Intent**: `Φ+,+` is finite on an injective interval
  - **Role**: main asymmetry lemma

- `finite_locPattern_mm`
  - **Intent**: `Φ-,-` is finite on an injective interval
  - **Role**: obtained from the previous one by applying it to `-f`

### H3.3 Upgrade from local pattern to global monotonicity

- `strictMonoOn_of_locPattern_mp`
  - **Intent**: if `Φ-,+` holds everywhere on an interval, then `f` is
    `StrictMonoOn` there
  - **Role**: last part of Coste's second step

- `strictAntiOn_of_locPattern_pm`
  - **Intent**: if `Φ+,-` holds everywhere on an interval, then `f` is
    `StrictAntiOn` there
  - **Role**: symmetric decreasing case

- `exists_strictMonoOrAntiOn_Ioo_of_injectiveOn`
  - **Intent**: package the whole second step of Coste 2.2
  - **Role**: clean handoff into the continuity step

### H3.4 Interval image and preimage under strict monotonicity

- `image_infinite_of_strictMonoOn_Ioo`
  - **Intent**: the image of a nontrivial interval under a strictly monotone map
    is infinite
  - **Role**: starts the last step of Coste 2.2

- `exists_Ioo_subset_range_of_strictMonoOn`
  - **Intent**: extract an interval from the image of a strictly monotone
    definable interval map
  - **Role**: constructs `J`

- `preimage_Ioo_of_strictMonoOn_is_interval`
  - **Intent**: the preimage of an open interval under a strict monotone map is
    an open interval
  - **Role**: used to replace the domain by `f⁻¹(J)`

- `continuousOn_of_strictMonoOn_bijective_Ioo`
  - **Intent**: a strictly monotone bijection between intervals is continuous
  - **Role**: conclusion of Coste 2.2

- `exists_const_or_strictMono_continuousOn_Ioo`
  - **Intent**: package the full statement of Coste 2.2 as the final helper
    theorem before Coste 2.1
  - **Role**: this becomes the core internal theorem that monotonicity uses

## Dependency Order Inside the Helper Stack

The helper order is fixed:

1. H1.1 local interval extraction
2. H1.2 finite-set and subdivision support
3. H1.3 o-minimal interval extraction
4. H2.1 fiber finiteness from non-constancy
5. H2.2 minimum selector
6. H2.3 packaged injectivity extraction
7. H3.1 local pattern predicates
8. H3.2 finiteness of `Φ+,+` and `Φ-,-`
9. H3.3 upgrade to strict monotonicity
10. H3.4 image/preimage and continuity of strict monotone interval maps

No later helper in H2 or H3 should be implemented before H1.3 is settled,
because Coste's proof repeatedly uses the “infinite definable subset of `ℝ`
contains an interval” move.

## Interface Notes for Future Lean Code

- Keep these lemmas internal to the future `Chapter2.Monotonicity` module.
- The public theorem currently called `oneVarEventuallyContinuous` in
  `Ominimal.lean` is **not** Coste 2.2; its docstring should be corrected when
  code changes resume.
- The implementation should prove an internal subdivision theorem first and
  derive the current exported `monotonicity` shape afterward.

## Acceptance Criteria

This inventory is complete only if:

- every helper used in `T1`–`T3` of `ONE_VARIABLE_CHECKLIST.md` is named;
- each helper has a clear proof role;
- the order of implementation is fixed;
- there is a named final helper theorem corresponding to the actual content of
  Coste 2.2;
- no helper still hides a major unplanned argument behind vague wording like
  “show” or “prove somehow.”

## Immediate Follow-On

After this document is accepted, the next planning or implementation pass
should start actual Lean work at H1.1 and proceed in the dependency order above.
