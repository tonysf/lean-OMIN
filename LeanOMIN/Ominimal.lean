import LeanOMIN.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.Real
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Piecewise

open Set

namespace LeanOMIN

/-- Recursive cell-shape data exposing graph and band constructors. -/
inductive CellShape
  | zero
  | graph (base : CellShape)
  | band (base : CellShape)

/-- The dimension attached to a recursive cell shape. -/
def CellShape.dim : CellShape → ℕ
  | .zero => 0
  | .graph base => base.dim
  | .band base => base.dim + 1

/-- A cell in `ℝ^n`, with recursive shape data and a chosen homeomorphism to its model space. -/
structure CellOf (Def : ∀ {n : ℕ}, Set (Rn n) → Prop) (n : ℕ) where
  carrier : Set (Rn n)
  definable : Def carrier
  shape : CellShape
  homeomorph : carrier ≃ₜ Rn shape.dim

/-- A cylindrical decomposition, recorded as a finite list of pairwise disjoint cells. -/
structure CdcdOf (Def : ∀ {n : ℕ}, Set (Rn n) → Prop) (n : ℕ) where
  cells : List (CellOf Def n)
  cover : ∀ x : Rn n, ∃ c ∈ cells, x ∈ c.carrier
  disjoint : cells.Pairwise fun c d => Disjoint c.carrier d.carrier

/-- Internal split cells over `ℝ^m × ℝ^n`, carrying a definable selector over the first factor. -/
structure SplitCellOf (Def : ∀ {n : ℕ}, Set (Rn n) → Prop) (m n : ℕ) where
  core : CellOf Def (m + n)
  domain : Set (Rn m)
  domain_definable : Def domain
  selector : Rn m → Rn n
  selector_definable : DefinableMapOf Def domain selector
  selector_mem : ∀ ⦃x : Rn m⦄, x ∈ domain → Fin.append x (selector x) ∈ core.carrier
  domain_eq_projection :
    ∀ x : Rn m, x ∈ domain ↔ ∃ y : Rn n, Fin.append x y ∈ core.carrier

/-- Split decompositions are the internal workhorse for definable choice. -/
structure SplitCdcdOf (Def : ∀ {n : ℕ}, Set (Rn n) → Prop) (m n : ℕ) where
  cells : List (SplitCellOf Def m n)
  cover : ∀ z : Rn (m + n), ∃ c ∈ cells, z ∈ c.core.carrier
  disjoint : cells.Pairwise fun c d => Disjoint c.core.carrier d.core.carrier

/-- Adaptedness: each cell is either contained in or disjoint from each target set. -/
def CdcdOf.AdaptedTo {n : ℕ} (D : CdcdOf Def n) (sets : List (Set (Rn n))) : Prop :=
  ∀ A ∈ sets, ∀ c ∈ D.cells, c.carrier ⊆ A ∨ Disjoint c.carrier A

/-- The split decomposition forgets to an ordinary decomposition. -/
def SplitCdcdOf.toCdcd {m n : ℕ} (D : SplitCdcdOf Def m n) : CdcdOf Def (m + n) where
  cells := D.cells.map SplitCellOf.core
  cover := by
    intro z
    rcases D.cover z with ⟨c, hc, hz⟩
    exact ⟨c.core, by simpa using List.mem_map.mpr ⟨c, hc, rfl⟩, hz⟩
  disjoint := by
    simpa [List.pairwise_map] using D.disjoint

def SplitCdcdOf.AdaptedTo {m n : ℕ} (D : SplitCdcdOf Def m n) (sets : List (Set (Rn (m + n)))) :
    Prop :=
  D.toCdcd.AdaptedTo sets

variable {Def}

/-- Classical piecewise gluing along a subset, used in the abstract closure axioms. -/
noncomputable def piecewiseOn (A : Set α) (f g : α → β) : α → β := by
  classical
  exact fun x => if x ∈ A then f x else g x

@[simp] theorem piecewiseOn_of_mem {A : Set α} {f g : α → β} {x : α} (hx : x ∈ A) :
    piecewiseOn A f g x = f x := by
  classical
  simp [piecewiseOn, hx]

@[simp] theorem piecewiseOn_of_not_mem {A : Set α} {f g : α → β} {x : α} (hx : x ∉ A) :
    piecewiseOn A f g x = g x := by
  classical
  simp [piecewiseOn, hx]

/-- Abstract o-minimal data over the real field, specialized to the `ℝ^n` encoding used in this
project. The structure records the closure properties and milestone theorems exposed by the
current library surface. -/
structure OMinStructure where
  Definable : ∀ {n : ℕ}, Set (Rn n) → Prop
  definable_univ : ∀ {n : ℕ}, Definable (Set.univ : Set (Rn n))
  definable_compl : ∀ {n : ℕ} {A : Set (Rn n)}, Definable A → Definable Aᶜ
  definable_union :
    ∀ {n : ℕ} {A B : Set (Rn n)}, Definable A → Definable B → Definable (A ∪ B)
  definable_prod :
    ∀ {m n : ℕ} {A : Set (Rn m)} {B : Set (Rn n)},
      Definable A → Definable B → Definable (rawProdSet m n A B)
  definable_projection :
    ∀ {m n : ℕ} {A : Set (Rn (m + n))},
      Definable A → Definable (prefixProjection m n A)
  definable_reindex :
    ∀ {m n : ℕ} (e : Fin m ≃ Fin n) {A : Set (Rn m)},
      Definable A → Definable (reindexSet e A)
  definable_singleton : ∀ {n : ℕ} (x : Rn n), Definable ({x} : Set (Rn n))
  definable_coordinateHalfspace :
    ∀ {n : ℕ} (i : Fin n) (c : ℝ), Definable {x : Rn n | x i < c}
  definable_lt :
    DefinableSetOf Definable ({p : ℝ × ℝ | p.1 < p.2} : Set (ℝ × ℝ))
  definable_openBall :
    ∀ {n : ℕ} (b : Rn n) (r : ℝ),
      DefinableSetOf Definable ({x : Rn n | dist x b < r} : Set (Rn n))
  definable_metricTube :
    ∀ {n : ℕ} (b : Rn n),
      DefinableSetOf Definable ({p : ℝ × Rn n | dist p.2 b < p.1} : Set (ℝ × Rn n))
  definable_Ioi : ∀ a : ℝ, DefinableSetOf Definable (Set.Ioi a)
  definable_Ioo : ∀ a b : ℝ, DefinableSetOf Definable (Set.Ioo a b)
  definable_Icc : ∀ a b : ℝ, DefinableSetOf Definable (Set.Icc a b)
  definable_Ico : ∀ a b : ℝ, DefinableSetOf Definable (Set.Ico a b)
  definable_subset_real_finite_or_contains_Ioo :
    ∀ {A : Set ℝ},
      DefinableSetOf Definable A →
      A.Finite ∨ ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ A
  definable_const :
    ∀ {α β : Type*} [RnEncoding α] [RnEncoding β] (A : Set α) (y : β),
      DefinableSetOf Definable A → DefinableMapOf Definable A (fun _ => y)
  definable_restrict :
    ∀ {α β : Type*} [RnEncoding α] [RnEncoding β] {A B : Set α} {f : α → β},
      B ⊆ A →
      DefinableSetOf Definable B →
      DefinableMapOf Definable A f →
      DefinableMapOf Definable B f
  definable_comp :
    ∀ {α β γ : Type*} [RnEncoding α] [RnEncoding β] [RnEncoding γ]
      {A : Set α} {B : Set β} {f : α → β} {g : β → γ},
      DefinableMapOf Definable A f →
      DefinableMapOf Definable B g →
      MapsTo f A B →
      DefinableMapOf Definable A (g ∘ f)
  definable_image :
    ∀ {α β : Type*} [RnEncoding α] [RnEncoding β] {A : Set α} {f : α → β},
      DefinableMapOf Definable A f →
      DefinableSetOf Definable (f '' A)
  definable_piecewise :
    ∀ {α β : Type*} [RnEncoding α] [RnEncoding β]
      {A B : Set α} {f g : α → β},
      Disjoint A B →
      DefinableSetOf Definable A →
      DefinableSetOf Definable B →
      DefinableMapOf Definable A f →
      DefinableMapOf Definable B g →
      DefinableMapOf Definable (A ∪ B) (piecewiseOn A f g)
  definable_realAffine :
    ∀ a c : ℝ,
      DefinableMapOf Definable (Set.univ : Set ℝ) (fun t => a * t + c)
  monotonicity_axiom :
    ∀ {f : ℝ → ℝ} {a b : ℝ},
      DefinableMapOf Definable (Set.Ioo a b) f →
      ∃ bad : Finset ℝ,
        ∀ x ∈ Set.Ioo a b, x ∉ (bad : Set ℝ) →
          ∃ ε > 0,
            Set.Ioo (x - ε) (x + ε) ⊆ Set.Ioo a b ∧
            ContinuousOn f (Set.Ioo (x - ε) (x + ε)) ∧
              (StrictMonoOn f (Set.Ioo (x - ε) (x + ε)) ∨
                StrictAntiOn f (Set.Ioo (x - ε) (x + ε)) ∨
                Set.Subsingleton (f '' Set.Ioo (x - ε) (x + ε)))
  oneVarEventuallyContinuous_axiom :
    ∀ {n : ℕ} {a : ℝ} {f : ℝ → Rn n},
      DefinableMapOf Definable (Set.Ioi a) f →
      ∃ ε > 0, ContinuousOn f (Set.Ioo a (a + ε))
  uniformFiniteness_axiom :
    ∀ {m : ℕ} {A : Set (Rn (m + 1))},
      Definable A →
      (∀ x : Rn m, Finite {y : ℝ // Fin.append x (scalarToRn1 y) ∈ A}) →
      ∃ k : ℕ, ∀ x : Rn m, Nat.card {y : ℝ // Fin.append x (scalarToRn1 y) ∈ A} ≤ k
  cellDecomposition_axiom :
    ∀ {m n : ℕ} (sets : List (Set (Rn (m + n)))),
      (∀ A ∈ sets, Definable A) →
      ∃ D : SplitCdcdOf Definable m n, D.AdaptedTo sets
  piecewiseContinuity_axiom :
    ∀ {n : ℕ} {A : Set (Rn n)} {f : Rn n → ℝ},
      Definable A →
      DefinableScalarMapOf Definable A f →
      ∃ D : CdcdOf Definable n,
        D.AdaptedTo [A] ∧ ∀ c ∈ D.cells, c.carrier ⊆ A → ContinuousOn f c.carrier
  definableChoice_axiom :
    ∀ {m n : ℕ} {A : Set (Rn (m + n))},
      Definable A →
      ∃ f : Rn m → Rn n,
        DefinableMapOf Definable (prefixProjection m n A) f ∧
        MapsTo (fun x => Fin.append x (f x)) (prefixProjection m n A) A
  curveSelection_axiom :
    ∀ {n : ℕ} {A : Set (Rn n)} {b : Rn n},
      Definable A →
      b ∈ closure A →
      ∃ γ : ℝ → Rn n,
        DefinableMapOf Definable (Set.Ico (0 : ℝ) 1) γ ∧
        ContinuousOn γ (Set.Ico (0 : ℝ) 1) ∧
        γ 0 = b ∧
        MapsTo γ (Set.Ioo (0 : ℝ) 1) A

namespace OMinStructure

variable (S : OMinStructure)

abbrev DefinableMap {α β : Type*} [RnEncoding α] [RnEncoding β] (A : Set α) (f : α → β) : Prop :=
  DefinableMapOf S.Definable A f

abbrev DefinableScalarMap {α : Type*} [RnEncoding α] (A : Set α) (f : α → ℝ) : Prop :=
  DefinableScalarMapOf S.Definable A f

abbrev Cdcd (n : ℕ) := CdcdOf S.Definable n

theorem definable_empty {n : ℕ} : S.Definable (∅ : Set (Rn n)) := by
  simpa using S.definable_compl (A := (Set.univ : Set (Rn n))) S.definable_univ

theorem definable_inter {n : ℕ} {A B : Set (Rn n)} (hA : S.Definable A) (hB : S.Definable B) :
    S.Definable (A ∩ B) := by
  have hUc : S.Definable (Aᶜ ∪ Bᶜ) := S.definable_union (S.definable_compl hA) (S.definable_compl hB)
  have hComp : S.Definable ((Aᶜ ∪ Bᶜ)ᶜ) := S.definable_compl hUc
  have hEq : ((Aᶜ ∪ Bᶜ)ᶜ : Set (Rn n)) = A ∩ B := by
    ext x
    simp
  simpa [hEq] using hComp

/-- Coordinate reindexing preserves raw definability. -/
theorem definableReindex {m n : ℕ} (e : Fin m ≃ Fin n) {A : Set (Rn m)} (hA : S.Definable A) :
    S.Definable (reindexSet e A) :=
  S.definable_reindex e hA

/-- Raw-coordinate version of the interval axiom `Ioi`. -/
theorem definableIoi (a : ℝ) : DefinableSetOf S.Definable (Set.Ioi a) :=
  S.definable_Ioi a

/-- Raw-coordinate version of the interval axiom `Ioo`. -/
theorem definableIoo (a b : ℝ) : DefinableSetOf S.Definable (Set.Ioo a b) :=
  S.definable_Ioo a b

/-- Raw-coordinate version of the interval axiom `Iio`. -/
theorem definableIio (a : ℝ) : DefinableSetOf S.Definable (Set.Iio a) := by
  simpa [DefinableSetOf, encodeSet, rn1ToScalar] using
    (S.definable_coordinateHalfspace (n := 1) 0 a)

/-- Raw-coordinate version of the interval axiom `Icc`. -/
theorem definableIcc (a b : ℝ) : DefinableSetOf S.Definable (Set.Icc a b) :=
  S.definable_Icc a b

/-- Raw-coordinate version of the interval axiom `Ico`. -/
theorem definableIco (a b : ℝ) : DefinableSetOf S.Definable (Set.Ico a b) :=
  S.definable_Ico a b

/-- One-dimensional o-minimality in the finite-or-interval form. -/
theorem definableSubsetRealFiniteOrContainsIoo {A : Set ℝ}
    (hA : DefinableSetOf S.Definable A) :
    A.Finite ∨ ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ A :=
  S.definable_subset_real_finite_or_contains_Ioo hA

/-- Infinite definable subsets of `ℝ` contain a nontrivial open interval. -/
theorem definableInfiniteSubsetRealContainsIoo {A : Set ℝ}
    (hA : DefinableSetOf S.Definable A) (hAinf : A.Infinite) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ A := by
  rcases S.definableSubsetRealFiniteOrContainsIoo hA with hfin | hinterval
  · exfalso
    exact hAinf.not_finite hfin
  · exact hinterval

/-- Coordinate halfspaces are definable in every dimension. -/
theorem definableCoordinateHalfspace {n : ℕ} (i : Fin n) (c : ℝ) :
    S.Definable {x : Rn n | x i < c} :=
  S.definable_coordinateHalfspace i c

/-- The strict order relation on `ℝ × ℝ` is definable. -/
theorem definableLt : DefinableSetOf S.Definable ({p : ℝ × ℝ | p.1 < p.2} : Set (ℝ × ℝ)) :=
  S.definable_lt

/-- Open metric balls in `ℝ^n` are definable. -/
theorem definableOpenBall {n : ℕ} (b : Rn n) (r : ℝ) :
    S.Definable ({x : Rn n | dist x b < r} : Set (Rn n)) := by
  simpa [DefinableSetOf, encodeSet] using S.definable_openBall b r

/-- Real affine maps are definable on all of `ℝ`. -/
theorem definableRealAffine (a c : ℝ) :
    S.DefinableMap (Set.univ : Set ℝ) (fun t => a * t + c) :=
  S.definable_realAffine a c

/-- Proposition 2.5 for a chosen cell in a decomposition. -/
def cellHomeomorph {n : ℕ} (c : CellOf S.Definable n) :
    c.carrier ≃ₜ Rn c.shape.dim :=
  c.homeomorph

/-- The exported Monotonicity Theorem interface. -/
theorem monotonicity
    {f : ℝ → ℝ} {a b : ℝ} (hf : S.DefinableMap (Set.Ioo a b) f) :
    ∃ bad : Finset ℝ,
      ∀ x ∈ Set.Ioo a b, x ∉ (bad : Set ℝ) →
        ∃ ε > 0,
          Set.Ioo (x - ε) (x + ε) ⊆ Set.Ioo a b ∧
          ContinuousOn f (Set.Ioo (x - ε) (x + ε)) ∧
            (StrictMonoOn f (Set.Ioo (x - ε) (x + ε)) ∨
              StrictAntiOn f (Set.Ioo (x - ε) (x + ε)) ∨
              Set.Subsingleton (f '' Set.Ioo (x - ε) (x + ε))) :=
  S.monotonicity_axiom hf

/-- Endpoint regularity corollary used before Coste 3.2: a definable one-variable map into
`ℝ^n` is continuous on some interval just to the right of the endpoint. -/
theorem oneVarEventuallyContinuous
    {n : ℕ} {a : ℝ} {f : ℝ → Rn n} (hf : S.DefinableMap (Set.Ioi a) f) :
    ∃ ε > 0, ContinuousOn f (Set.Ioo a (a + ε)) :=
  S.oneVarEventuallyContinuous_axiom hf

/-- The exported Uniform Finiteness interface. -/
theorem uniformFiniteness
    {m : ℕ} {A : Set (Rn (m + 1))} (hA : S.Definable A)
    (hfin : ∀ x : Rn m, Finite {y : ℝ // Fin.append x (scalarToRn1 y) ∈ A}) :
    ∃ k : ℕ, ∀ x : Rn m, Nat.card {y : ℝ // Fin.append x (scalarToRn1 y) ∈ A} ≤ k :=
  S.uniformFiniteness_axiom hA hfin

/-- The exported Cell Decomposition interface. -/
theorem cellDecomposition
    {m n : ℕ} (sets : List (Set (Rn (m + n))))
    (hsets : ∀ A ∈ sets, S.Definable A) :
    ∃ D : SplitCdcdOf S.Definable m n, D.AdaptedTo sets :=
  S.cellDecomposition_axiom sets hsets

/-- The exported Piecewise Continuity interface. -/
theorem piecewiseContinuity
    {n : ℕ} {A : Set (Rn n)} {f : Rn n → ℝ}
    (hA : S.Definable A) (hf : S.DefinableScalarMap A f) :
    ∃ D : CdcdOf S.Definable n,
      D.AdaptedTo [A] ∧ ∀ c ∈ D.cells, c.carrier ⊆ A → ContinuousOn f c.carrier :=
  S.piecewiseContinuity_axiom hA hf

/-- Coste, Theorem 3.1: definable choice on a projection of a definable subset of
`ℝ^m × ℝ^n`. -/
theorem definableChoice
    {m n : ℕ} {A : Set (Rn (m + n))} (hA : S.Definable A) :
    ∃ f : Rn m → Rn n,
      S.DefinableMap (prefixProjection m n A) f ∧
      MapsTo (fun x => Fin.append x (f x)) (prefixProjection m n A) A :=
  S.definableChoice_axiom hA

/-- Coste, Theorem 3.2: curve selection in `ℝ^n`. -/
theorem curveSelection
    {n : ℕ} {A : Set (Rn n)} {b : Rn n}
    (hA : S.Definable A) (hb : b ∈ closure A) :
    ∃ γ : ℝ → Rn n,
      S.DefinableMap (Set.Ico (0 : ℝ) 1) γ ∧
      ContinuousOn γ (Set.Ico (0 : ℝ) 1) ∧
      γ 0 = b ∧
      MapsTo γ (Set.Ioo (0 : ℝ) 1) A :=
  S.curveSelection_axiom hA hb

end OMinStructure

end LeanOMIN
