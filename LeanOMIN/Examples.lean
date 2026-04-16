import LeanOMIN.Ominimal

open Set

namespace LeanOMIN

/-- The encoded graph cell associated to a map `f : A → ℝ^n`. -/
def graphCell {m n : ℕ} (A : Set (Rn m)) (f : Rn m → Rn n) : Set (Rn (m + n)) :=
  encodeSet (Rn m × Rn n) (rawGraph A f)

/-- An encoded bounded band over a base set. -/
def boundedBand {m : ℕ} (A : Set (Rn m)) (f g : Rn m → ℝ) : Set (Rn (m + 1)) :=
  encodeSet (Rn m × ℝ) {p : Rn m × ℝ | p.1 ∈ A ∧ f p.1 < p.2 ∧ p.2 < g p.1}

/-- An encoded half-infinite band over a base set. -/
def halfInfiniteBand {m : ℕ} (A : Set (Rn m)) (f : Rn m → ℝ) : Set (Rn (m + 1)) :=
  encodeSet (Rn m × ℝ) {p : Rn m × ℝ | p.1 ∈ A ∧ f p.1 < p.2}

/-- The punctured open ball in `ℝ¹` centered at the origin. -/
def puncturedBallAtOrigin1D (r : ℝ) : Set (Rn 1) :=
  {x : Rn 1 | x ≠ 0 ∧ dist x 0 < r}

theorem scalarToRn1_ne_zero {t : ℝ} (ht : t ≠ 0) : scalarToRn1 t ≠ (0 : Rn 1) := by
  intro h
  apply ht
  have h0 := congrFun h 0
  simpa [scalarToRn1] using h0

theorem dist_scalarToRn1_zero_lt {t ε : ℝ} (ht0 : 0 ≤ t) (htε : t < ε) :
    dist (scalarToRn1 t) (0 : Rn 1) < ε := by
  have hε : 0 < ε := lt_of_le_of_lt ht0 htε
  rw [dist_pi_lt_iff hε]
  intro i
  have hi : i = 0 := Fin.eq_zero i
  simpa [scalarToRn1, hi, Real.dist_eq, abs_of_nonneg ht0] using htε

/-- The origin lies in the closure of every positive-radius punctured ball in `ℝ¹`. -/
theorem zero_mem_closure_puncturedBallAtOrigin1D {r : ℝ} (hr : 0 < r) :
    (0 : Rn 1) ∈ closure (puncturedBallAtOrigin1D r) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min (ε / 2) (r / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hε) (half_pos hr)
  let y : Rn 1 := scalarToRn1 δ
  refine ⟨y, ?_, ?_⟩
  · constructor
    · simpa [y] using scalarToRn1_ne_zero (ne_of_gt hδpos)
    · have hδr : δ < r := by
        dsimp [δ]
        exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr)
      simpa [y] using dist_scalarToRn1_zero_lt (le_of_lt hδpos) hδr
  · have hδε : δ < ε := by
      dsimp [δ]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    simpa [y, dist_comm] using dist_scalarToRn1_zero_lt (le_of_lt hδpos) hδε

namespace OMinStructure

variable (S : OMinStructure)

/-- Sanity check: affine maps are part of the exported definable API. -/
theorem affineMap_example (a c : ℝ) :
    S.DefinableMap (Set.univ : Set ℝ) (fun t => a * t + c) :=
  S.definableRealAffine a c

/-- Sanity check: coordinate halfspaces are definable. -/
theorem coordinateHalfspace_example {n : ℕ} (i : Fin n) (c : ℝ) :
    S.Definable {x : Rn n | x i < c} :=
  S.definableCoordinateHalfspace i c

/-- Sanity check: open metric balls are definable. -/
theorem openBall_example {n : ℕ} (b : Rn n) (r : ℝ) :
    S.Definable ({x : Rn n | dist x b < r} : Set (Rn n)) :=
  S.definableOpenBall b r

/-- Sanity check for definable choice on a graph cell. -/
theorem graphCell_choice_example {m n : ℕ} {A : Set (Rn m)} {f : Rn m → Rn n}
    (hf : S.DefinableMap A f) :
    ∃ g : Rn m → Rn n,
      S.DefinableMap (prefixProjection m n (graphCell A f)) g ∧
      MapsTo (fun x => Fin.append x (g x)) (prefixProjection m n (graphCell A f)) (graphCell A f) := by
  have hGraph : S.Definable (graphCell A f) := by
    simpa [graphCell, DefinableMapOf, DefinableSetOf] using hf
  exact S.definableChoice hGraph

/-- Sanity check for definable choice on a bounded band, once the band is known definable. -/
theorem boundedBand_choice_example {m : ℕ} {A : Set (Rn m)} {f g : Rn m → ℝ}
    (hBand : S.Definable (boundedBand A f g)) :
    ∃ h : Rn m → Rn 1,
      S.DefinableMap (prefixProjection m 1 (boundedBand A f g)) h ∧
      MapsTo (fun x => Fin.append x (h x)) (prefixProjection m 1 (boundedBand A f g))
        (boundedBand A f g) :=
  S.definableChoice hBand

/-- Sanity check for definable choice on a half-infinite band, once the band is known definable. -/
theorem halfInfiniteBand_choice_example {m : ℕ} {A : Set (Rn m)} {f : Rn m → ℝ}
    (hBand : S.Definable (halfInfiniteBand A f)) :
    ∃ h : Rn m → Rn 1,
      S.DefinableMap (prefixProjection m 1 (halfInfiniteBand A f)) h ∧
      MapsTo (fun x => Fin.append x (h x)) (prefixProjection m 1 (halfInfiniteBand A f))
        (halfInfiniteBand A f) :=
  S.definableChoice hBand

/-- Sanity check for curve selection in an open ball. -/
theorem curveSelection_openBall_example {n : ℕ} (b : Rn n) {r : ℝ} (hr : 0 < r) :
    ∃ γ : ℝ → Rn n,
      S.DefinableMap (Set.Ico (0 : ℝ) 1) γ ∧
      ContinuousOn γ (Set.Ico (0 : ℝ) 1) ∧
      γ 0 = b ∧
      MapsTo γ (Set.Ioo (0 : ℝ) 1) ({x : Rn n | dist x b < r} : Set (Rn n)) := by
  have hbIn : b ∈ ({x : Rn n | dist x b < r} : Set (Rn n)) := by
    simpa [dist_self] using hr
  exact S.curveSelection (A := ({x : Rn n | dist x b < r} : Set (Rn n))) (b := b)
    (S.definableOpenBall b r) (subset_closure hbIn)

/-- Sanity check for curve selection at a point already lying in the target set. -/
theorem curveSelection_mem_example {n : ℕ} {A : Set (Rn n)} {b : Rn n}
    (hA : S.Definable A) (hb : b ∈ A) :
    ∃ γ : ℝ → Rn n,
      S.DefinableMap (Set.Ico (0 : ℝ) 1) γ ∧
      ContinuousOn γ (Set.Ico (0 : ℝ) 1) ∧
      γ 0 = b ∧
      MapsTo γ (Set.Ioo (0 : ℝ) 1) A :=
  S.curveSelection hA (subset_closure hb)

/-- The punctured one-dimensional ball is definable from the abstract API. -/
theorem definable_puncturedBallAtOrigin1D (r : ℝ) :
    S.Definable (puncturedBallAtOrigin1D r) := by
  have hBall : S.Definable ({x : Rn 1 | dist x (0 : Rn 1) < r} : Set (Rn 1)) :=
    S.definableOpenBall 0 r
  have hNonzero : S.Definable (({(0 : Rn 1)} : Set (Rn 1))ᶜ) :=
    S.definable_compl (S.definable_singleton 0)
  have hEq :
      puncturedBallAtOrigin1D r =
        ({x : Rn 1 | dist x (0 : Rn 1) < r} : Set (Rn 1)) ∩ ({(0 : Rn 1)} : Set (Rn 1))ᶜ := by
    ext x
    simp [puncturedBallAtOrigin1D, and_comm]
  simpa [hEq] using S.definable_inter hBall hNonzero

/-- Sanity check for curve selection at the origin of a punctured one-dimensional ball. -/
theorem curveSelection_puncturedBallAtOrigin1D_example {r : ℝ} (hr : 0 < r) :
    ∃ γ : ℝ → Rn 1,
      S.DefinableMap (Set.Ico (0 : ℝ) 1) γ ∧
      ContinuousOn γ (Set.Ico (0 : ℝ) 1) ∧
      γ 0 = 0 ∧
      MapsTo γ (Set.Ioo (0 : ℝ) 1) (puncturedBallAtOrigin1D r) :=
  S.curveSelection (A := puncturedBallAtOrigin1D r) (b := 0)
    (S.definable_puncturedBallAtOrigin1D r)
    (zero_mem_closure_puncturedBallAtOrigin1D hr)

end OMinStructure

end LeanOMIN
