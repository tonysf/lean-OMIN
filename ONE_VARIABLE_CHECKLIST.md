# One-Variable Checklist

Detailed implementation checklist for the first proof tranche in the roadmap:
the one-variable layer behind Coste 2.2, Coste 2.1, Exercise 2.3, and the
eventual-continuity corollary currently exported as
`oneVarEventuallyContinuous`.

This document is narrower than `ROADMAP.md`. It does not plan the whole route
to curve selection; it fixes the execution order for the first theorem package
to implement.

The symbol-level helper inventory for tasks `T1` through `T3` lives in
[`ONE_VARIABLE_HELPERS.md`](ONE_VARIABLE_HELPERS.md).

## Goal

Replace the current one-variable placeholders in `OMinStructure` with actual
proofs over the existing abstract o-minimal interface on `ℝ`.

This stage must end with:

- an internal proof of Coste 2.2
- an internal proof of Coste 2.1
- a proved one-sided limit corollary matching Coste Exercise 2.3
- a proved vector-valued eventual continuity theorem
- retirement of:
  - `monotonicity_axiom`
  - `oneVarEventuallyContinuous_axiom`

This stage must **not** yet try to prove:

- `uniformFiniteness`
- `cellDecomposition`
- `piecewiseContinuity`
- `definableChoice`
- `curveSelection`

## Current Boundary

The current API already provides the primitives this stage is allowed to use:

- `S.DefinableMap`
- interval definability on `ℝ`
- `definable_const`, `definable_restrict`, `definable_comp`,
  `definable_piecewise`
- `definableRealAffine`

The implementation should introduce a future chapter module:

- `LeanOMIN/Chapter2/Monotonicity.lean`

For now, the checklist should be read as if that module will eventually feed
back into `LeanOMIN/Ominimal.lean`, which stays the public re-export surface.

## Deliverables

### D1. Internal statement for Coste 2.2

Add an internal theorem expressing the actual content of Lemma 2.2:

- input: definable `f : (a,b) → ℝ`
- output: there exists a nonempty open subinterval of `(a,b)` on which `f` is
  constant, or there exists a nonempty open subinterval on which `f` is
  strictly monotone and continuous

This theorem should be internal support for `monotonicity`; it does not need to
be exported from the top-level API under a polished public name yet.

### D2. Proof of Coste 2.1

Replace `monotonicity_axiom` by an actual proof of the exported theorem
`monotonicity`.

The exported theorem shape may stay as it is now, even though Coste states the
result as a finite subdivision. The implementation should prove the stronger
subdivision-style internal theorem first, then derive the current exported
formulation from it.

### D3. One-sided limit corollary

Add an internal theorem matching Exercise 2.3:

- for definable `f : (a,b) → ℝ`, both `lim x -> a+` and `lim x -> b-` exist in
  `ℝ ∪ {−∞, +∞}`

This theorem is a bridge result. It is not the end goal, but it should be
formalized explicitly rather than buried inside the proof of eventual
continuity.

### D4. Vector eventual continuity

Replace `oneVarEventuallyContinuous_axiom` by a proof that:

- if `f : ℝ → Rn n` is definable on `Ioi a`, then there exists `ε > 0` such
  that `f` is continuous on `Ioo a (a + ε)`

This result should be proved coordinatewise from the scalar one-variable
package.

## Proof Order

The implementation order is fixed:

1. one-dimensional interval and finite-set support lemmas
2. finite-fiber minimum selection on `ℝ`
3. injective-interval image/preimage lemmas
4. Coste 2.2
5. Coste 2.1 in subdivision form
6. derivation of the current exported `monotonicity`
7. Exercise 2.3 one-sided limits
8. vector eventual continuity
9. retirement of `monotonicity_axiom`
10. retirement of `oneVarEventuallyContinuous_axiom`

Do not start the Chapter 2 simultaneous induction package until all ten items
above are complete.

## Task Breakdown

### T1. Interval helper layer

Formalize the interval facts used repeatedly in Coste 2.2 and 2.1.

Required facts:

- nonempty subinterval extraction inside `Ioo a b`
- shrinking an interval while preserving membership in `Ioo a b`
- if a definable subset of `ℝ` is infinite, it contains a nonempty open
  interval
- finite definable subsets of `ℝ` can be separated by a finite subdivision
- the complement of a finite subset of an interval is a finite union of open
  intervals

Expected role:

- supports the first step of Lemma 2.2
- supports the subdivision conclusion in Theorem 2.1

### T2. Finite-fiber choice on `ℝ`

Formalize the minimum-selection device used in Coste's first step of Lemma 2.2.

Required facts:

- if every fiber `f⁻¹(y)` is finite, then the set-valued map
  `y ↦ {x | f x = y}` admits a definable minimum selector on its nonempty locus
- the minimum selector is definable on its domain
- if `f ∘ g = id` on an interval, then `g` is injective

Expected role:

- produces the interval `J` and the selector `g : J → (a,b)` used to extract an
  interval of injectivity for `f`

### T3. Injective interval-map layer

Formalize the interval geometry of an injective definable map between
intervals.

Required facts:

- the image of an interval under an injective definable map contains an
  interval when the image is infinite
- the preimage of an interval under a strictly monotone map is an interval
- if `f : I → J` is a strictly monotone bijection between intervals, then `f`
  is continuous
- if the inverse image of every subinterval of `J` is a subinterval of `I`,
  continuity follows

Expected role:

- supports the last step of Lemma 2.2

### T4. Coste 2.2, step 1: extract injectivity

Implement the first step exactly as Coste presents it.

Checklist:

1. Assume `f` is not constant on any subinterval.
2. Prove every fiber `f⁻¹(y)` is finite.
3. Prove the image `f '' I` is infinite.
4. Extract a nonempty interval `J` in the image.
5. Define `g(y) = min(f⁻¹(y))`.
6. Prove `f ∘ g = id` on `J`.
7. Use the image of `g` to extract a subinterval `I` on which `f` is injective.

Acceptance condition:

- the implementation produces an explicit lemma of the form “if `f` is not
  locally constant on any interval, then `f` is injective on some subinterval.”

### T5. Coste 2.2, step 2: extract strict monotonicity

Implement the four-pattern argument.

Checklist:

1. Define `I+`, `I-`.
2. Define the four local-pattern predicates `Φ+,+`, `Φ+,-`, `Φ-,+`, `Φ-,-`.
3. Prove they form a definable partition of the injectivity interval.
4. Formalize the contradiction proof that `Φ+,+` is finite.
5. Mirror the argument for `Φ-,-` by replacing `f` with `-f`.
6. Shrink to an interval where only `Φ-,+` or `Φ+,-` holds.
7. Upgrade the pointwise local pattern to global strict increase or decrease
   via the least-upper-bound argument.

Hidden sublemmas that must be explicit:

- if a definable subset of an interval is infinite, it contains a subinterval
- a nonempty finite definable subset of an interval has a maximum
- the `Ψ+,-` / `Ψ-,+` contradiction mechanism can be packaged as a reusable
  local-order lemma

Acceptance condition:

- the implementation produces an explicit lemma of the form “injective definable
  maps on an interval are strictly monotone on some subinterval.”

### T6. Coste 2.2, step 3: upgrade to continuity

Implement the final step.

Checklist:

1. Start from the strictly monotone interval obtained in T5.
2. Show the image is infinite, hence contains a nonempty interval `J`.
3. Replace the domain interval by `f⁻¹(J)`.
4. Prove the restricted map is a strictly monotone bijection onto `J`.
5. Invoke the injective interval-map layer from T3 to conclude continuity.

Acceptance condition:

- the full statement of Coste 2.2 is proved.

### T7. Coste 2.1: subdivision theorem

Prove an internal subdivision form of monotonicity first.

Checklist:

1. Define the local behavior sets:
   - points where `f` is locally constant
   - points where `f` is locally strictly increasing and continuous
   - points where `f` is locally strictly decreasing and continuous
2. Prove the complement is finite by contradiction with Coste 2.2.
3. Enumerate that finite complement into an ordered subdivision.
4. Show each open interval between consecutive breakpoints lies entirely in one
   of the three local behavior sets.
5. Upgrade local behavior on that interval to global behavior by the least-upper-bound argument.

Acceptance condition:

- obtain an internal theorem equivalent to Coste's finite-subdivision
  formulation.

### T8. Derive the exported `monotonicity`

The current public theorem is not phrased as a subdivision theorem; it gives a
finite bad set and local continuous monotonicity data around each good point.

Checklist:

1. Start from the subdivision theorem proved in T7.
2. Let the bad set be the finite set of subdivision points.
3. For every point not in the bad set, choose the unique subdivision interval
   containing it.
4. Produce an `ε > 0` witness lying inside that interval.
5. Derive the current exported disjunction:
   - `StrictMonoOn`
   - `StrictAntiOn`
   - image subsingleton

Acceptance condition:

- `monotonicity_axiom` can be removed and the current theorem name
  `monotonicity` remains unchanged.

### T9. Exercise 2.3: one-sided limits

Formalize the endpoint-limit corollary after monotonicity is available.

Checklist:

1. Restrict to the final subdivision interval adjacent to `a` or `b`.
2. Reduce to the cases:
   - constant
   - strictly increasing
   - strictly decreasing
3. Show one-sided limits exist in the extended real line in each case.

Acceptance condition:

- this result is available as a standalone theorem and not hidden inside the
  proof of vector eventual continuity.

### T10. Vector eventual continuity near an endpoint

Use the scalar package to prove the currently exported theorem
`oneVarEventuallyContinuous`.

Checklist:

1. Apply the scalar one-variable theorem to each coordinate of
   `f : ℝ → Fin n → ℝ`.
2. For each coordinate, obtain a witness interval on which the coordinate is
   continuous.
3. Take the minimum positive radius over all coordinates.
4. Prove continuity of `f` on the common interval by coordinatewise continuity.

Acceptance condition:

- `oneVarEventuallyContinuous_axiom` can be removed without changing the public
  theorem name or theorem statement.

## Naming and Interface Decisions

Use the following naming policy during implementation:

- keep the public names `monotonicity` and `oneVarEventuallyContinuous`
- keep Coste numbers in docstrings
- for internal helper lemmas, prefer descriptive Lean names over theorem-number
  names

Examples of acceptable internal names:

- `exists_injective_on_subinterval`
- `exists_strictMonoOrAntiOn_subinterval`
- `exists_const_or_strictMono_continuous_subinterval`
- `exists_rightLimitAt_of_definable`

Do not expose the full internal helper stack from `LeanOMIN.lean` unless later
chapters genuinely need it.

## Tests and Verification

This checklist is complete only if the following verification points are built
into the eventual implementation work:

- `lake build` still passes after each retirement step
- the exported theorem names and statement shapes remain stable
- the examples depending on `monotonicity` and `oneVarEventuallyContinuous`
  continue to compile without modification
- no new theorem-shaped `_axiom` fields are introduced to get around missing
  one-variable lemmas

## Immediate Follow-On

After this checklist is accepted, the next document or implementation pass
should follow the dependency order in
[`ONE_VARIABLE_HELPERS.md`](ONE_VARIABLE_HELPERS.md) starting at `H1.1`.
