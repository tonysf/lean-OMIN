import LeanOMIN.Ominimal
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

open Set

namespace LeanOMIN

/-- Swap the two coordinates of `ℝ²`. -/
def swapFin2 : Fin 2 ≃ Fin 2 :=
  Equiv.swap 0 1

/-- Swap the last two coordinates of `ℝ³`. -/
def swapFin3Tail : Fin 3 ≃ Fin 3 :=
  Equiv.swap 1 2

/-- Swap the middle two coordinates of `ℝ⁴`. -/
def swapFin4Mid : Fin 4 ≃ Fin 4 :=
  Equiv.swap 1 2

@[simp] theorem reindexRn_swapFin2_fin_append (x y : Rn 1) :
    (reindexRn swapFin2).symm (Fin.append x y) = Fin.append y x := by
  funext i
  fin_cases i
  · change y 0 = y 0
    rfl
  · change x 0 = x 0
    rfl

/-- Swap the last two coordinates of a triple `(y, x, z)`. -/
@[simp] theorem reindexRn_swapFin3Tail_triple (y x z : Rn 1) :
    (reindexRn swapFin3Tail).symm (Fin.append (Fin.append y x) z) =
      Fin.append (Fin.append y z) x := by
  funext i
  fin_cases i <;> rfl

/-- Swap the middle coordinates of a quadruple `(x, fx, y, fy)`. -/
@[simp] theorem reindexRn_swapFin4Mid_quad (x fx y fy : Rn 1) :
    (reindexRn swapFin4Mid).symm (Fin.append (Fin.append x fx) (Fin.append y fy)) =
      Fin.append (Fin.append x y) (Fin.append fx fy) := by
  funext i
  fin_cases i <;> rfl

/-- Internal H1.3 wrapper: a definable subset of `ℝ` is either finite or contains a nontrivial
open interval. -/
theorem definable_subset_real_finite_or_contains_Ioo {S : OMinStructure} {A : Set ℝ}
    (hA : DefinableSetOf S.Definable A) :
    A.Finite ∨ ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ A :=
  S.definableSubsetRealFiniteOrContainsIoo hA

/-- Internal H1.3 wrapper: every infinite definable subset of `ℝ` contains an open interval. -/
theorem definable_infinite_subset_real_contains_Ioo {S : OMinStructure} {A : Set ℝ}
    (hA : DefinableSetOf S.Definable A) (hAinf : A.Infinite) :
    ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ A :=
  S.definableInfiniteSubsetRealContainsIoo hA hAinf

/-- The image of a definable real-valued map on an interval is definable. -/
theorem definable_image_of_definableMap {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (f '' Set.Ioo a b) := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let Gswap : Set (Rn 2) := reindexSet swapFin2 G
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hGswap : S.Definable Gswap :=
    S.definableReindex swapFin2 hG
  have hProj : S.Definable (prefixProjection 1 1 Gswap) :=
    S.definable_projection hGswap
  have hEq : prefixProjection 1 1 Gswap = encodeSet ℝ (f '' Set.Ioo a b) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨w, hw⟩
      have hw' : Fin.append w x ∈ G := by
        simpa [Gswap, reindexSet, reindexRn_swapFin2_fin_append] using hw
      have hw'' : rn1ToScalar w ∈ Set.Ioo a b ∧ rn1ToScalar x = f (rn1ToScalar w) := by
        simpa [G, rawGraph] using hw'
      refine ⟨rn1ToScalar w, hw''.1, ?_⟩
      simpa [rn1ToScalar_scalarToRn1] using hw''.2.symm
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      have hxeq : x = scalarToRn1 (f y) := by
        have hx0 : x = scalarToRn1 (rn1ToScalar x) := by
          simpa using (scalarToRn1_rn1ToScalar x).symm
        have hyx' : rn1ToScalar x = f y := by
          simpa [RnEncoding.equiv, realEquivRn1] using hyx.symm
        exact hx0.trans (by simpa [hyx'])
      refine ⟨scalarToRn1 y, ?_⟩
      have hgraph : (y, f y) ∈ rawGraph (Set.Ioo a b) f := by
        exact ⟨hy, rfl⟩
      have hgraph' : Fin.append (scalarToRn1 y) (scalarToRn1 (f y)) ∈ G := by
        simpa [G] using hgraph
      rw [hxeq]
      simpa [Gswap, reindexSet, reindexRn_swapFin2_fin_append] using hgraph'
  simpa [hEq] using hProj

/-- Raw pair relation `(y, x)` expressing `x ∈ (a,b)` and `f x = y`. -/
def pairFiberRel (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  reindexSet swapFin2 (encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f))

/-- The raw pair relation `(y, x)` attached to a definable one-variable map is definable. -/
theorem definable_pairFiberRel {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (pairFiberRel f a b) := by
  have hG : S.Definable (encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)) := by
    simpa [DefinableMapOf, DefinableSetOf] using hf
  exact S.definableReindex swapFin2 hG

@[simp] theorem fin_append_mem_pairFiberRel {f : ℝ → ℝ} {a b : ℝ} {y x : Rn 1} :
    Fin.append y x ∈ pairFiberRel f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧ rn1ToScalar y = f (rn1ToScalar x) := by
  rw [pairFiberRel, mem_reindexSet]
  rw [reindexRn_swapFin2_fin_append, mem_encodeSet_real_prod, splitAtEquiv_fin_append]
  simp [rawGraph]

@[simp] theorem fin_append_mem_ltPairSet {u v : Rn 1} :
    Fin.append u v ∈ encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2} ↔
      rn1ToScalar u < rn1ToScalar v := by
  rw [mem_encodeSet_real_prod, splitAtEquiv_fin_append]
  simp

@[simp] theorem fin_append_assoc_rn1 (u v w : Rn 1) :
    Fin.append (Fin.append u v) w = Fin.append u (Fin.append v w) := by
  funext i
  fin_cases i <;> rfl

/-- Raw triples `(y, x, z)` with `x` and `z` in the same fiber and `z < x`. -/
def badFiberTripleSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 3) :=
  let P := pairFiberRel f a b
  let Cx := rawProdSet 2 1 P (Set.univ : Set (Rn 1))
  let Cz := reindexSet swapFin3Tail (rawProdSet 2 1 P (Set.univ : Set (Rn 1)))
  let LtZX :=
    reindexSet swapFin3Tail
      (rawProdSet 1 2 (Set.univ : Set (Rn 1))
        (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}))
  Cx ∩ Cz ∩ LtZX

/-- The bad-triple witness set is definable. -/
theorem definable_badFiberTripleSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (badFiberTripleSet f a b) := by
  let P := pairFiberRel f a b
  let Cx := rawProdSet 2 1 P (Set.univ : Set (Rn 1))
  let Cz := reindexSet swapFin3Tail (rawProdSet 2 1 P (Set.univ : Set (Rn 1)))
  let LtZX :=
    reindexSet swapFin3Tail
      (rawProdSet 1 2 (Set.univ : Set (Rn 1))
        (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}))
  have hP : S.Definable P := definable_pairFiberRel (S := S) (f := f) (a := a) (b := b) hf
  have hCx : S.Definable Cx := by
    dsimp [Cx, P]
    exact S.definable_prod hP S.definable_univ
  have hCz : S.Definable Cz := by
    dsimp [Cz, P]
    exact S.definableReindex swapFin3Tail (S.definable_prod hP S.definable_univ)
  have hLtRaw : S.Definable (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) := by
    simpa [DefinableSetOf] using S.definableLt
  have hLtZX : S.Definable LtZX := by
    dsimp [LtZX]
    exact S.definableReindex swapFin3Tail (S.definable_prod S.definable_univ hLtRaw)
  dsimp [badFiberTripleSet, Cx, Cz, LtZX, P]
  exact S.definable_inter (S.definable_inter hCx hCz) hLtZX

/-- Raw pairs `(y, x)` admitting a smaller witness in the same fiber. -/
def badFiberPairSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  prefixProjection 2 1 (badFiberTripleSet f a b)

/-- The bad-pair witness set is definable. -/
theorem definable_badFiberPairSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (badFiberPairSet f a b) :=
  S.definable_projection (definable_badFiberTripleSet (S := S) (f := f) (a := a) (b := b) hf)

/-- Raw minimal pairs `(y, x)` in which `x` is a fiber point with no smaller witness. -/
def minimalFiberPairSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  pairFiberRel f a b ∩ (badFiberPairSet f a b)ᶜ

/-- The raw minimal-pair set is definable. -/
theorem definable_minimalFiberPairSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (minimalFiberPairSet f a b) := by
  exact S.definable_inter
    (definable_pairFiberRel (S := S) (f := f) (a := a) (b := b) hf)
    (S.definable_compl (definable_badFiberPairSet (S := S) (f := f) (a := a) (b := b) hf))

@[simp] theorem fin_append_triple_mem_badFiberTripleSet
    {f : ℝ → ℝ} {a b : ℝ} {y x z : Rn 1} :
    Fin.append (Fin.append y x) z ∈ badFiberTripleSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar y = f (rn1ToScalar x) ∧
      rn1ToScalar z ∈ Set.Ioo a b ∧
      rn1ToScalar y = f (rn1ToScalar z) ∧
      rn1ToScalar z < rn1ToScalar x := by
  dsimp [badFiberTripleSet]
  rw [mem_inter_iff, mem_inter_iff]
  rw [mem_rawProdSet, splitAtEquiv_fin_append, fin_append_mem_pairFiberRel]
  rw [mem_reindexSet, reindexRn_swapFin3Tail_triple, mem_rawProdSet, splitAtEquiv_fin_append,
    fin_append_mem_pairFiberRel]
  rw [mem_reindexSet, reindexRn_swapFin3Tail_triple, fin_append_assoc_rn1, mem_rawProdSet,
    splitAtEquiv_fin_append,
    fin_append_mem_ltPairSet]
  simp [and_assoc, and_left_comm, and_comm]

@[simp] theorem fin_append_mem_badFiberPairSet
    {f : ℝ → ℝ} {a b : ℝ} {y x : Rn 1} :
    Fin.append y x ∈ badFiberPairSet f a b ↔
      ∃ z : ℝ,
        z ∈ Set.Ioo a b ∧
        rn1ToScalar y = f z ∧
        z < rn1ToScalar x ∧
        rn1ToScalar x ∈ Set.Ioo a b ∧
        rn1ToScalar y = f (rn1ToScalar x) := by
  constructor
  · intro hx
    rcases hx with ⟨z, hz⟩
    rcases (fin_append_triple_mem_badFiberTripleSet (y := y) (x := x) (z := z)).mp hz with
      ⟨hxIoo, hyx, hzIoo, hyz, hzx⟩
    exact ⟨rn1ToScalar z, hzIoo, hyz, hzx, hxIoo, hyx⟩
  · rintro ⟨z, hzIoo, hyz, hzx, hxIoo, hyx⟩
    refine ⟨scalarToRn1 z, ?_⟩
    simpa [rn1ToScalar_scalarToRn1] using
      (fin_append_triple_mem_badFiberTripleSet (y := y) (x := x) (z := scalarToRn1 z)).2
        ⟨hxIoo, hyx, by simpa using hzIoo, by simpa using hyz, hzx⟩

@[simp] theorem fin_append_mem_minimalFiberPairSet
    {f : ℝ → ℝ} {a b : ℝ} {y x : Rn 1} :
    Fin.append y x ∈ minimalFiberPairSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar y = f (rn1ToScalar x) ∧
      ∀ z : ℝ, z ∈ Set.Ioo a b → rn1ToScalar y = f z → ¬ z < rn1ToScalar x := by
  rw [minimalFiberPairSet, mem_inter_iff, fin_append_mem_pairFiberRel, mem_compl_iff,
    fin_append_mem_badFiberPairSet]
  constructor
  · rintro ⟨⟨hxIoo, hyx⟩, hbad⟩
    refine ⟨hxIoo, hyx, ?_⟩
    intro z hzIoo hyz hzx
    exact hbad ⟨z, hzIoo, hyz, hzx, hxIoo, hyx⟩
  · rintro ⟨hxIoo, hyx, hmin⟩
    refine ⟨⟨hxIoo, hyx⟩, ?_⟩
    rintro ⟨z, hzIoo, hyz, hzx, -, -⟩
    exact hmin z hzIoo hyz hzx

/-- Fibers of a definable real-valued map on an interval are definable. -/
theorem definable_fiber_eq_of_definableMap {S : OMinStructure} {f : ℝ → ℝ} {a b y : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable {x : ℝ | x ∈ Set.Ioo a b ∧ f x = y} := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let H : Set (Rn 2) :=
    rawProdSet 1 1 (Set.univ : Set (Rn 1)) ({scalarToRn1 y} : Set (Rn 1))
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hH : S.Definable H := by
    simpa [H] using
      S.definable_prod (A := (Set.univ : Set (Rn 1))) (B := ({scalarToRn1 y} : Set (Rn 1)))
        S.definable_univ (S.definable_singleton (scalarToRn1 y))
  have hProj : S.Definable (prefixProjection 1 1 (G ∩ H)) :=
    S.definable_projection (S.definable_inter hG hH)
  have hEq :
      prefixProjection 1 1 (G ∩ H) =
        encodeSet ℝ {x : ℝ | x ∈ Set.Ioo a b ∧ f x = y} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨w, hw⟩
      have hwG : Fin.append x w ∈ G := hw.1
      have hwH : Fin.append x w ∈ H := hw.2
      have hwG' : rn1ToScalar x ∈ Set.Ioo a b ∧ rn1ToScalar w = f (rn1ToScalar x) := by
        simpa [G, rawGraph] using hwG
      have hwH'' : w = scalarToRn1 y := by
        have hwH' :
            (splitAtEquiv 1 1 (Fin.append x w)).2 ∈ ({scalarToRn1 y} : Set (Rn 1)) := by
          have hwHraw :
              Fin.append x w ∈
                rawProdSet 1 1 (Set.univ : Set (Rn 1)) ({scalarToRn1 y} : Set (Rn 1)) := by
            simpa [H] using hwH
          exact (mem_rawProdSet.mp hwHraw).2
        have hsplit : (splitAtEquiv 1 1 (Fin.append x w)).2 = w := by
          simpa using congrArg Prod.snd (splitAtEquiv_fin_append x w)
        exact hsplit.symm ▸ (by simpa using hwH')
      have hx' : rn1ToScalar x ∈ {x : ℝ | x ∈ Set.Ioo a b ∧ f x = y} := by
        refine ⟨hwG'.1, ?_⟩
        rw [← rn1ToScalar_scalarToRn1 y, ← hwH'', hwG'.2]
      simpa using hx'
    · intro hx
      refine ⟨scalarToRn1 y, ?_⟩
      constructor
      · have hx' : rn1ToScalar x ∈ {x : ℝ | x ∈ Set.Ioo a b ∧ f x = y} := by
          simpa using hx
        have hgraph :
            (rn1ToScalar x, rn1ToScalar (scalarToRn1 y)) ∈ rawGraph (Set.Ioo a b) f := by
          simpa [rawGraph, eq_comm] using hx'
        simpa [G, rawGraph] using hgraph
      · change
          Fin.append x (scalarToRn1 y) ∈
            rawProdSet 1 1 (Set.univ : Set (Rn 1)) ({scalarToRn1 y} : Set (Rn 1))
        rw [mem_rawProdSet]
        refine ⟨by simp, ?_⟩
        simpa using congrArg Prod.snd (splitAtEquiv_fin_append x (scalarToRn1 y))
  simpa [hEq] using hProj

/-- Strict lower level sets of a definable real-valued interval map are definable. -/
theorem definable_ltLevelSet_of_definableMap {S : OMinStructure} {f : ℝ → ℝ} {a b y : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable {x : ℝ | x ∈ Set.Ioo a b ∧ f x < y} := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let H : Set (Rn 2) :=
    rawProdSet 1 1 (Set.univ : Set (Rn 1)) (encodeSet ℝ (Set.Iio y))
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hH : S.Definable H := by
    dsimp [H]
    exact S.definable_prod S.definable_univ
      (by simpa [DefinableSetOf] using S.definableIio y)
  have hProj : S.Definable (prefixProjection 1 1 (G ∩ H)) :=
    S.definable_projection (S.definable_inter hG hH)
  have hEq :
      prefixProjection 1 1 (G ∩ H) =
        encodeSet ℝ {x : ℝ | x ∈ Set.Ioo a b ∧ f x < y} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨w, hw⟩
      have hwG : Fin.append x w ∈ G := hw.1
      have hwH : Fin.append x w ∈ H := hw.2
      have hwG' : rn1ToScalar x ∈ Set.Ioo a b ∧ rn1ToScalar w = f (rn1ToScalar x) := by
        simpa [G, rawGraph] using hwG
      have hwH' : rn1ToScalar w ∈ Set.Iio y := by
        have hwH'' :
            Fin.append x w ∈
              rawProdSet 1 1 (Set.univ : Set (Rn 1)) (encodeSet ℝ (Set.Iio y)) := by
          simpa [H] using hwH
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real] at hwH''
        simpa using hwH''.2
      have hx' : rn1ToScalar x ∈ {x : ℝ | x ∈ Set.Ioo a b ∧ f x < y} := by
        refine ⟨hwG'.1, ?_⟩
        simpa [hwG'.2] using hwH'
      simpa [mem_encodeSet_real] using hx'
    · intro hx
      have hx' : rn1ToScalar x ∈ {x : ℝ | x ∈ Set.Ioo a b ∧ f x < y} := by
        simpa [mem_encodeSet_real] using hx
      refine ⟨scalarToRn1 (f (rn1ToScalar x)), ?_⟩
      constructor
      · have hgraph :
            (rn1ToScalar x, rn1ToScalar (scalarToRn1 (f (rn1ToScalar x)))) ∈
              rawGraph (Set.Ioo a b) f := by
          exact ⟨hx'.1, by simp⟩
        dsimp [G]
        rw [mem_encodeSet_real_prod, splitAtEquiv_fin_append]
        simpa [rn1ToScalar_scalarToRn1] using hgraph
      · change
          Fin.append x (scalarToRn1 (f (rn1ToScalar x))) ∈
            rawProdSet 1 1 (Set.univ : Set (Rn 1)) (encodeSet ℝ (Set.Iio y))
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real]
        exact ⟨by simp, by simpa [rn1ToScalar_scalarToRn1] using hx'.2⟩
  simpa [hEq] using hProj

/-- Strict upper level sets of a definable real-valued interval map are definable. -/
theorem definable_gtLevelSet_of_definableMap {S : OMinStructure} {f : ℝ → ℝ} {a b y : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable {x : ℝ | x ∈ Set.Ioo a b ∧ y < f x} := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let H : Set (Rn 2) :=
    rawProdSet 1 1 (Set.univ : Set (Rn 1)) (encodeSet ℝ (Set.Ioi y))
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hH : S.Definable H := by
    dsimp [H]
    exact S.definable_prod S.definable_univ
      (by simpa [DefinableSetOf] using S.definableIoi y)
  have hProj : S.Definable (prefixProjection 1 1 (G ∩ H)) :=
    S.definable_projection (S.definable_inter hG hH)
  have hEq :
      prefixProjection 1 1 (G ∩ H) =
        encodeSet ℝ {x : ℝ | x ∈ Set.Ioo a b ∧ y < f x} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨w, hw⟩
      have hwG : Fin.append x w ∈ G := hw.1
      have hwH : Fin.append x w ∈ H := hw.2
      have hwG' : rn1ToScalar x ∈ Set.Ioo a b ∧ rn1ToScalar w = f (rn1ToScalar x) := by
        simpa [G, rawGraph] using hwG
      have hwH' : rn1ToScalar w ∈ Set.Ioi y := by
        have hwH'' :
            Fin.append x w ∈
              rawProdSet 1 1 (Set.univ : Set (Rn 1)) (encodeSet ℝ (Set.Ioi y)) := by
          simpa [H] using hwH
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real] at hwH''
        simpa using hwH''.2
      have hx' : rn1ToScalar x ∈ {x : ℝ | x ∈ Set.Ioo a b ∧ y < f x} := by
        refine ⟨hwG'.1, ?_⟩
        simpa [hwG'.2] using hwH'
      simpa [mem_encodeSet_real] using hx'
    · intro hx
      have hx' : rn1ToScalar x ∈ {x : ℝ | x ∈ Set.Ioo a b ∧ y < f x} := by
        simpa [mem_encodeSet_real] using hx
      refine ⟨scalarToRn1 (f (rn1ToScalar x)), ?_⟩
      constructor
      · have hgraph :
            (rn1ToScalar x, rn1ToScalar (scalarToRn1 (f (rn1ToScalar x)))) ∈
              rawGraph (Set.Ioo a b) f := by
          exact ⟨hx'.1, by simp⟩
        dsimp [G]
        rw [mem_encodeSet_real_prod, splitAtEquiv_fin_append]
        simpa [rn1ToScalar_scalarToRn1] using hgraph
      · change
          Fin.append x (scalarToRn1 (f (rn1ToScalar x))) ∈
            rawProdSet 1 1 (Set.univ : Set (Rn 1)) (encodeSet ℝ (Set.Ioi y))
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real]
        exact ⟨by simp, by simpa [rn1ToScalar_scalarToRn1] using hx'.2⟩
  simpa [hEq] using hProj

/-- Shrink an ambient open interval to a smaller open interval still containing a chosen point. -/
theorem exists_Ioo_subset_of_mem_Ioo {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
    ∃ u v : ℝ, x ∈ Set.Ioo u v ∧ Set.Ioo u v ⊆ Set.Ioo a b := by
  rcases hx with ⟨hax, hxb⟩
  rcases exists_between hax with ⟨u, hau, hux⟩
  rcases exists_between hxb with ⟨v, hxv, hvb⟩
  refine ⟨u, v, ⟨hux, hxv⟩, ?_⟩
  intro y hy
  exact ⟨lt_trans hau hy.1, lt_trans hy.2 hvb⟩

/-- Every point of an open interval admits a symmetric smaller interval still contained in the
ambient one. -/
theorem exists_small_Ioo_around_mem_Ioo {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
    ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ⊆ Set.Ioo a b := by
  rcases hx with ⟨hax, hxb⟩
  let ε : ℝ := min (x - a) (b - x) / 2
  have hxa : 0 < x - a := sub_pos.mpr hax
  have hbx : 0 < b - x := sub_pos.mpr hxb
  have hmin : 0 < min (x - a) (b - x) := lt_min hxa hbx
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hεlt_min : ε < min (x - a) (b - x) := by
    dsimp [ε]
    simpa using half_lt_self hmin
  have hεlt_left : ε < x - a := lt_of_lt_of_le hεlt_min (min_le_left _ _)
  have hεlt_right : ε < b - x := lt_of_lt_of_le hεlt_min (min_le_right _ _)
  have hleft : a < x - ε := by
    linarith
  have hright : x + ε < b := by
    linarith
  refine ⟨ε, hεpos, ?_⟩
  intro y hy
  constructor
  · exact lt_trans hleft hy.1
  · exact lt_trans hy.2 hright

namespace Set.Finite

/-- A nonempty finite subset of `ℝ` has a least element. The interval-flavoured name matches the
later one-variable roadmap, although the statement itself does not need interval hypotheses. -/
theorem subset_interval_has_min {s : Set ℝ} (hs : s.Finite) (hne : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, x ≤ y := by
  classical
  let t : Finset ℝ := hs.toFinset
  have htne : t.Nonempty := by
    simpa [t] using hs.toFinset_nonempty.mpr hne
  refine ⟨t.min' htne, ?_, ?_⟩
  · exact hs.mem_toFinset.mp (Finset.min'_mem t htne)
  · intro y hy
    exact Finset.min'_le t y (hs.mem_toFinset.mpr hy)

/-- A nonempty finite subset of `ℝ` has a greatest element. The interval-flavoured name matches
the later one-variable roadmap, although the statement itself does not need interval hypotheses. -/
theorem subset_interval_has_max {s : Set ℝ} (hs : s.Finite) (hne : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  classical
  let t : Finset ℝ := hs.toFinset
  have htne : t.Nonempty := by
    simpa [t] using hs.toFinset_nonempty.mpr hne
  refine ⟨t.max' htne, ?_, ?_⟩
  · exact hs.mem_toFinset.mp (Finset.max'_mem t htne)
  · intro y hy
    exact Finset.le_max' t y (hs.mem_toFinset.mpr hy)

end Set.Finite

/-- If a definable real-valued map is nonconstant on every nontrivial subinterval of `(a,b)`,
then each fiber over `(a,b)` is finite. -/
theorem fiber_finite_of_no_const_subinterval {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hNoConst :
      ∀ u v : ℝ, Set.Ioo u v ⊆ Set.Ioo a b → u < v →
        ¬ Set.Subsingleton (f '' Set.Ioo u v)) :
    ∀ y : ℝ, ({x : ℝ | x ∈ Set.Ioo a b ∧ f x = y} : Set ℝ).Finite := by
  intro y
  have hFiberDef :
      DefinableSetOf S.Definable ({x : ℝ | x ∈ Set.Ioo a b ∧ f x = y} : Set ℝ) :=
    definable_fiber_eq_of_definableMap (S := S) (f := f) (a := a) (b := b) (y := y) hf
  rcases definable_subset_real_finite_or_contains_Ioo (S := S) hFiberDef with hfin | hIoo
  · exact hfin
  · rcases hIoo with ⟨u, v, huv, huvSub⟩
    exfalso
    have hSubDom : Set.Ioo u v ⊆ Set.Ioo a b := by
      intro x hx
      exact (huvSub hx).1
    have hSubsingleton : Set.Subsingleton (f '' Set.Ioo u v) := by
      intro z hz w hw
      rcases hz with ⟨xz, hxz, rfl⟩
      rcases hw with ⟨xw, hxw, rfl⟩
      rw [(huvSub hxz).2, (huvSub hxw).2]
    exact hNoConst u v hSubDom huv hSubsingleton

/-- If a definable real-valued map is nonconstant on every nontrivial subinterval of `(a,b)`,
then its image on `(a,b)` is infinite. -/
theorem image_infinite_of_no_const_subinterval {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hNoConst :
      ∀ u v : ℝ, Set.Ioo u v ⊆ Set.Ioo a b → u < v →
        ¬ Set.Subsingleton (f '' Set.Ioo u v)) :
    (f '' Set.Ioo a b).Infinite := by
  intro hImgFin
  let g : Set.Ioo a b → ℝ := fun x => f x
  have hFiberFinite := fiber_finite_of_no_const_subinterval (S := S) (f := f) (a := a) (b := b)
    hf hNoConst
  have hRangeEq : Set.range g = f '' Set.Ioo a b := by
    ext y
    simp [g]
  have hRangeFinite : (Set.range g).Finite := by
    simpa [hRangeEq] using hImgFin
  have hPreimageFinite :
      ∀ y ∈ Set.range g, (g ⁻¹' ({y} : Set ℝ)).Finite := by
    intro y hy
    let e : Set.Ioo a b ↪ ℝ := ⟨Subtype.val, Subtype.val_injective⟩
    have hBase : ({x : ℝ | x ∈ Set.Ioo a b ∧ f x = y} : Set ℝ).Finite := hFiberFinite y
    have hEmbFinite :
        ({x : Set.Ioo a b | e x ∈ ({x : ℝ | x ∈ Set.Ioo a b ∧ f x = y} : Set ℝ)}).Finite :=
      Set.Finite.preimage_embedding e hBase
    exact hEmbFinite.subset (by
      intro x hx
      exact ⟨x.2, hx⟩)
  have hDomainFinite : (g ⁻¹' Set.range g).Finite :=
    Set.Finite.preimage' hRangeFinite hPreimageFinite
  have hUnivFinite : (Set.univ : Set (Set.Ioo a b)).Finite := by
    exact hDomainFinite.subset (by
      intro x hx
      exact ⟨x, rfl⟩)
  letI : Infinite (Set.Ioo a b) := Set.Ioo.infinite hab
  exact (Set.infinite_univ : (Set.univ : Set (Set.Ioo a b)).Infinite).not_finite hUnivFinite

/-- Under the same hypotheses, the image contains a nontrivial open interval. -/
theorem exists_Ioo_subset_image_of_no_const_subinterval
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hNoConst :
      ∀ u v : ℝ, Set.Ioo u v ⊆ Set.Ioo a b → u < v →
        ¬ Set.Subsingleton (f '' Set.Ioo u v)) :
    ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ f '' Set.Ioo a b := by
  have hImgDef := definable_image_of_definableMap (S := S) (f := f) (a := a) (b := b) hf
  have hImgInf :=
    image_infinite_of_no_const_subinterval (S := S) (f := f) (a := a) (b := b) hab hf hNoConst
  exact definable_infinite_subset_real_contains_Ioo (S := S) hImgDef hImgInf

/-- The fiber of `f` over `y` inside `(a,b)`. -/
def fiberEqOn (f : ℝ → ℝ) (a b y : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Ioo a b ∧ f x = y}

/-- The locus of values hit by `f` on `(a,b)`. -/
def fiberMinDomain (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  f '' Set.Ioo a b

/-- The minimum point in the fiber of `f` over `y`, when that fiber is nonempty and finite.
Outside the image domain we return `0`, but later uses will always restrict to the domain. -/
noncomputable def fiberMin (f : ℝ → ℝ) (a b : ℝ)
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) (y : ℝ) : ℝ :=
  by
    classical
    exact if hy : y ∈ fiberMinDomain f a b then
      Classical.choose <| Set.Finite.subset_interval_has_min (hfin y) <| by
        rcases hy with ⟨x, hx, rfl⟩
        exact ⟨x, ⟨hx, rfl⟩⟩
    else
      0

/-- On its natural domain, `fiberMin` lies in the required fiber. -/
theorem fiberMin_mem {f : ℝ → ℝ} {a b : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) {y : ℝ}
    (hy : y ∈ fiberMinDomain f a b) :
    fiberMin f a b hfin y ∈ fiberEqOn f a b y := by
  classical
  unfold fiberMin
  simp [hy]
  exact (Classical.choose_spec
    (Set.Finite.subset_interval_has_min (hfin y) (by
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx, rfl⟩⟩))).1

/-- On its natural domain, `fiberMin` picks a point of `(a,b)` mapping to `y`. -/
theorem fiberMin_spec {f : ℝ → ℝ} {a b : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) {y : ℝ}
    (hy : y ∈ fiberMinDomain f a b) :
    fiberMin f a b hfin y ∈ Set.Ioo a b ∧ f (fiberMin f a b hfin y) = y :=
  fiberMin_mem hfin hy

/-- On its natural domain, `fiberMin` is a left inverse for `f`. -/
theorem fiberMin_leftInverseOn {f : ℝ → ℝ} {a b : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) :
    ∀ y ∈ fiberMinDomain f a b, f (fiberMin f a b hfin y) = y := by
  intro y hy
  exact (fiberMin_spec hfin hy).2

/-- On its natural domain, `fiberMin` is the least point of the fiber. -/
theorem fiberMin_le {f : ℝ → ℝ} {a b : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) {y x : ℝ}
    (hy : y ∈ fiberMinDomain f a b) (hx : x ∈ fiberEqOn f a b y) :
    fiberMin f a b hfin y ≤ x := by
  classical
  unfold fiberMin
  simp [hy]
  exact (Classical.choose_spec
    (Set.Finite.subset_interval_has_min (hfin y) (by
      rcases hy with ⟨x0, hx0, rfl⟩
      exact ⟨x0, ⟨hx0, rfl⟩⟩))).2 x hx

@[simp] theorem fin_append_mem_fiberMinGraph
    {f : ℝ → ℝ} {a b : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) {y x : Rn 1} :
    Fin.append y x ∈
        encodeSet (ℝ × ℝ) (rawGraph (fiberMinDomain f a b) (fiberMin f a b hfin)) ↔
      rn1ToScalar y ∈ fiberMinDomain f a b ∧
        rn1ToScalar x = fiberMin f a b hfin (rn1ToScalar y) := by
  rw [mem_encodeSet_real_prod, splitAtEquiv_fin_append]
  simp [rawGraph]

/-- The raw minimal-pair set is exactly the graph of the minimum-fiber selector. -/
theorem fin_append_mem_minimalFiberPairSet_iff_mem_fiberMinGraph
    {f : ℝ → ℝ} {a b : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) {y x : Rn 1} :
    Fin.append y x ∈ minimalFiberPairSet f a b ↔
      Fin.append y x ∈
        encodeSet (ℝ × ℝ) (rawGraph (fiberMinDomain f a b) (fiberMin f a b hfin)) := by
  rw [fin_append_mem_minimalFiberPairSet, fin_append_mem_fiberMinGraph]
  constructor
  · rintro ⟨hxIoo, hyx, hmin⟩
    have hy : rn1ToScalar y ∈ fiberMinDomain f a b := ⟨rn1ToScalar x, hxIoo, hyx.symm⟩
    have hspec := fiberMin_spec hfin hy
    have hxfiber : rn1ToScalar x ∈ fiberEqOn f a b (rn1ToScalar y) := ⟨hxIoo, hyx.symm⟩
    have hminle : fiberMin f a b hfin (rn1ToScalar y) ≤ rn1ToScalar x :=
      fiberMin_le hfin hy hxfiber
    have hxle : rn1ToScalar x ≤ fiberMin f a b hfin (rn1ToScalar y) := by
      exact le_of_not_gt (hmin _ hspec.1 hspec.2.symm)
    exact ⟨hy, le_antisymm hxle hminle⟩
  · rintro ⟨hy, hxy⟩
    have hspec := fiberMin_spec hfin hy
    refine ⟨?_, ?_, ?_⟩
    · simpa [hxy] using hspec.1
    · simpa [hxy] using hspec.2.symm
    · intro z hzIoo hyz hzx
      have hzfiber : z ∈ fiberEqOn f a b (rn1ToScalar y) := ⟨hzIoo, hyz.symm⟩
      have hminle : fiberMin f a b hfin (rn1ToScalar y) ≤ z :=
        fiberMin_le hfin hy hzfiber
      exact (not_lt_of_ge (by simpa [hxy] using hminle)) hzx

/-- The minimum-fiber selector is definable on its natural image domain. -/
theorem definable_fiberMin {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) :
    DefinableMapOf S.Definable (fiberMinDomain f a b) (fiberMin f a b hfin) := by
  have hMin : S.Definable (minimalFiberPairSet f a b) :=
    definable_minimalFiberPairSet (S := S) (f := f) (a := a) (b := b) hf
  have hEq :
      minimalFiberPairSet f a b =
        encodeSet (ℝ × ℝ) (rawGraph (fiberMinDomain f a b) (fiberMin f a b hfin)) := by
    ext z
    let y : Rn 1 := (splitAtEquiv 1 1 z).1
    let x : Rn 1 := (splitAtEquiv 1 1 z).2
    have hz : Fin.append y x = z := by
      dsimp [y, x]
      rw [← splitAtEquiv_symm_apply]
      exact (splitAtEquiv 1 1).symm_apply_apply z
    rw [← hz]
    exact fin_append_mem_minimalFiberPairSet_iff_mem_fiberMinGraph hfin
  simpa [DefinableMapOf, DefinableSetOf, hEq] using hMin

/-- The image of the minimum-fiber selector on a subinterval of its domain is definable. -/
theorem definable_image_fiberMin_of_Ioo_subset_domain
    {S : OMinStructure} {f : ℝ → ℝ} {a b u v : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite)
    (hsub : Set.Ioo u v ⊆ fiberMinDomain f a b) :
    DefinableSetOf S.Definable (fiberMin f a b hfin '' Set.Ioo u v) := by
  let G : Set (Rn 2) :=
    encodeSet (ℝ × ℝ) (rawGraph (fiberMinDomain f a b) (fiberMin f a b hfin))
  let H : Set (Rn 2) :=
    rawProdSet 1 1 (encodeSet ℝ (Set.Ioo u v)) (Set.univ : Set (Rn 1))
  let Gcut : Set (Rn 2) := G ∩ H
  let Gswap : Set (Rn 2) := reindexSet swapFin2 Gcut
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using
      (definable_fiberMin (S := S) (f := f) (a := a) (b := b) hf hfin)
  have hH : S.Definable H := by
    dsimp [H]
    exact S.definable_prod (by simpa [DefinableSetOf] using S.definableIoo u v) S.definable_univ
  have hProj : S.Definable (prefixProjection 1 1 Gswap) := by
    exact S.definable_projection (S.definableReindex swapFin2 (S.definable_inter hG hH))
  have hEq : prefixProjection 1 1 Gswap = encodeSet ℝ (fiberMin f a b hfin '' Set.Ioo u v) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨w, hw⟩
      have hw' : Fin.append w x ∈ Gcut := by
        simpa [Gswap, reindexSet, reindexRn_swapFin2_fin_append] using hw
      have hwG : Fin.append w x ∈ G := hw'.1
      have hwH : Fin.append w x ∈ H := hw'.2
      have hwG' :
          rn1ToScalar w ∈ fiberMinDomain f a b ∧
            rn1ToScalar x = fiberMin f a b hfin (rn1ToScalar w) := by
        simpa [G] using
          (fin_append_mem_fiberMinGraph (hfin := hfin) (y := w) (x := x)).mp hwG
      have hwH' : rn1ToScalar w ∈ Set.Ioo u v := by
        have hwH' :
            Fin.append w x ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioo u v)) (Set.univ : Set (Rn 1)) := by
          simpa [H] using hwH
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real] at hwH'
        simpa using hwH'.1
      refine ⟨rn1ToScalar w, hwH', ?_⟩
      simpa [rn1ToScalar_scalarToRn1] using hwG'.2.symm
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyDom : y ∈ fiberMinDomain f a b := hsub hy
      have hxeq : x = scalarToRn1 (fiberMin f a b hfin y) := by
        have hx0 : x = scalarToRn1 (rn1ToScalar x) := by
          simpa using (scalarToRn1_rn1ToScalar x).symm
        have hyx' : rn1ToScalar x = fiberMin f a b hfin y := by
          simpa [RnEncoding.equiv, realEquivRn1] using hyx.symm
        exact hx0.trans (by simpa [hyx'])
      refine ⟨scalarToRn1 y, ?_⟩
      have hgraph : Fin.append (scalarToRn1 y) (scalarToRn1 (fiberMin f a b hfin y)) ∈ G := by
        dsimp [G]
        rw [mem_encodeSet_real_prod, splitAtEquiv_fin_append]
        exact ⟨hyDom, by simp [rn1ToScalar_scalarToRn1]⟩
      have hcut : Fin.append (scalarToRn1 y) (scalarToRn1 (fiberMin f a b hfin y)) ∈ Gcut := by
        have hHmem :
            Fin.append (scalarToRn1 y) (scalarToRn1 (fiberMin f a b hfin y)) ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioo u v)) (Set.univ : Set (Rn 1)) := by
          rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real]
          exact ⟨hy, Set.mem_univ _⟩
        refine ⟨hgraph, ?_⟩
        simpa [H] using hHmem
      rw [hxeq]
      simpa [Gswap, Gcut, reindexSet, reindexRn_swapFin2_fin_append] using hcut
  simpa [hEq] using hProj

/-- A left inverse on a set forces injectivity on that set. -/
theorem injective_of_leftInverse_on {α β : Type*} {A : Set α} {f : α → β} {g : β → α}
    (hleft : ∀ x ∈ A, g (f x) = x) :
    Set.InjOn f A := by
  intro x hx y hy hxy
  rw [← hleft x hx, ← hleft y hy, hxy]

/-- The minimum-fiber selector is injective on its natural domain. -/
theorem fiberMin_injOn {f : ℝ → ℝ} {a b : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite) :
    Set.InjOn (fiberMin f a b hfin) (fiberMinDomain f a b) :=
  injective_of_leftInverse_on (f := fiberMin f a b hfin) (g := f) (A := fiberMinDomain f a b)
    (fiberMin_leftInverseOn hfin)

/-- The image of an injective map on a nontrivial open interval is infinite. -/
theorem image_infinite_of_injectiveOn_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hinj : Set.InjOn f (Set.Ioo a b)) :
    (f '' Set.Ioo a b).Infinite :=
  (Set.Ioo_infinite hab).image hinj

/-- The image of an injective definable map on a nontrivial open interval contains a nontrivial
open interval. -/
theorem exists_Ioo_subset_image_of_injectiveOn_Ioo
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hinj : Set.InjOn f (Set.Ioo a b)) :
    ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ f '' Set.Ioo a b := by
  have hImgDef : DefinableSetOf S.Definable (f '' Set.Ioo a b) :=
    definable_image_of_definableMap (S := S) (f := f) (a := a) (b := b) hf
  have hImgInf : (f '' Set.Ioo a b).Infinite :=
    image_infinite_of_injectiveOn_Ioo hab hinj
  exact definable_infinite_subset_real_contains_Ioo (S := S) hImgDef hImgInf

/-- A strictly increasing map on a set is injective on that set. -/
theorem injOn_of_strictMonoOn {f : ℝ → ℝ} {s : Set ℝ} (hmono : StrictMonoOn f s) :
    Set.InjOn f s := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · exfalso
    exact (ne_of_lt (hmono hx hy hlt)) hxy
  · rfl
  · exfalso
    exact (ne_of_lt (hmono hy hx hgt)) hxy.symm

/-- A strictly decreasing map on a set is injective on that set. -/
theorem injOn_of_strictAntiOn {f : ℝ → ℝ} {s : Set ℝ} (hanti : StrictAntiOn f s) :
    Set.InjOn f s := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · exfalso
    exact (ne_of_gt (hanti hx hy hlt)) hxy
  · rfl
  · exfalso
    exact (ne_of_gt (hanti hy hx hgt)) hxy.symm

/-- The image of a strictly increasing map on a nontrivial open interval is infinite. -/
theorem image_infinite_of_strictMonoOn_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hmono : StrictMonoOn f (Set.Ioo a b)) :
    (f '' Set.Ioo a b).Infinite :=
  image_infinite_of_injectiveOn_Ioo hab (injOn_of_strictMonoOn hmono)

/-- The image of a strictly decreasing map on a nontrivial open interval is infinite. -/
theorem image_infinite_of_strictAntiOn_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hanti : StrictAntiOn f (Set.Ioo a b)) :
    (f '' Set.Ioo a b).Infinite :=
  image_infinite_of_injectiveOn_Ioo hab (injOn_of_strictAntiOn hanti)

/-- The image of a strictly increasing definable map on a nontrivial open interval contains a
nontrivial open interval. -/
theorem exists_Ioo_subset_image_of_strictMonoOn_Ioo
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hmono : StrictMonoOn f (Set.Ioo a b)) :
    ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ f '' Set.Ioo a b :=
  exists_Ioo_subset_image_of_injectiveOn_Ioo (S := S) hab hf (injOn_of_strictMonoOn hmono)

/-- The image of a strictly decreasing definable map on a nontrivial open interval contains a
nontrivial open interval. -/
theorem exists_Ioo_subset_image_of_strictAntiOn_Ioo
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hanti : StrictAntiOn f (Set.Ioo a b)) :
    ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ f '' Set.Ioo a b :=
  exists_Ioo_subset_image_of_injectiveOn_Ioo (S := S) hab hf (injOn_of_strictAntiOn hanti)

/-- A strictly increasing map on an open interval is continuous once its image is an open
interval. -/
theorem continuousOn_of_strictMonoOn_image_eq_Ioo
    {f : ℝ → ℝ} {a b c d : ℝ}
    (hmono : StrictMonoOn f (Set.Ioo a b))
    (himg : f '' Set.Ioo a b = Set.Ioo c d) :
    ContinuousOn f (Set.Ioo a b) := by
  intro x hx
  have hs : Set.Ioo a b ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
  have hfx : f x ∈ Set.Ioo c d := by
    rw [← himg]
    exact ⟨x, hx, rfl⟩
  have hfs : f '' Set.Ioo a b ∈ nhds (f x) := by
    rw [himg]
    exact IsOpen.mem_nhds isOpen_Ioo hfx
  exact (hmono.continuousAt_of_image_mem_nhds hs hfs).continuousWithinAt

/-- A strictly decreasing map on an open interval is continuous once its image is an open
interval. -/
theorem continuousOn_of_strictAntiOn_image_eq_Ioo
    {f : ℝ → ℝ} {a b c d : ℝ}
    (hanti : StrictAntiOn f (Set.Ioo a b))
    (himg : f '' Set.Ioo a b = Set.Ioo c d) :
    ContinuousOn f (Set.Ioo a b) := by
  let g : ℝ → ℝ := fun x => -f x
  have hgmono : StrictMonoOn g (Set.Ioo a b) := by
    intro x hx y hy hxy
    exact neg_lt_neg (hanti hx hy hxy)
  have hgimg : g '' Set.Ioo a b = Set.Ioo (-d) (-c) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hfx : f x ∈ Set.Ioo c d := by
        rw [← himg]
        exact ⟨x, hx, rfl⟩
      change -f x ∈ Set.Ioo (-d) (-c)
      constructor <;> linarith [hfx.1, hfx.2]
    · intro hy
      have hneg : -y ∈ Set.Ioo c d := by
        constructor <;> linarith [hy.1, hy.2]
      rw [← himg] at hneg
      rcases hneg with ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      change -f x = y
      linarith
  have hgcont : ContinuousOn g (Set.Ioo a b) :=
    continuousOn_of_strictMonoOn_image_eq_Ioo (f := g) hgmono hgimg
  intro x hx
  simpa [g] using (hgcont x hx).neg

/-- If an open interval lies in the domain of `fiberMin`, then the corresponding selector image
is infinite. -/
theorem fiberMin_image_infinite_of_Ioo_subset_domain {f : ℝ → ℝ} {a b u v : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite)
    (huv : u < v) (hsub : Set.Ioo u v ⊆ fiberMinDomain f a b) :
    (fiberMin f a b hfin '' Set.Ioo u v).Infinite := by
  exact image_infinite_of_injectiveOn_Ioo huv ((fiberMin_injOn hfin).mono hsub)

/-- If an open interval sits in the selector domain, then the selector image contains an open
subinterval. -/
theorem exists_Ioo_subset_fiberMin_image_of_Ioo_subset_domain
    {S : OMinStructure} {f : ℝ → ℝ} {a b u v : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite)
    (huv : u < v) (hsub : Set.Ioo u v ⊆ fiberMinDomain f a b) :
    ∃ r s : ℝ, r < s ∧ Set.Ioo r s ⊆ fiberMin f a b hfin '' Set.Ioo u v := by
  have hImgDef : DefinableSetOf S.Definable (fiberMin f a b hfin '' Set.Ioo u v) :=
    definable_image_fiberMin_of_Ioo_subset_domain
      (S := S) (f := f) (a := a) (b := b) (u := u) (v := v) hf hfin hsub
  have hImgInf : (fiberMin f a b hfin '' Set.Ioo u v).Infinite :=
    fiberMin_image_infinite_of_Ioo_subset_domain hfin huv hsub
  exact definable_infinite_subset_real_contains_Ioo (S := S) hImgDef hImgInf

/-- Any interval contained in the image of the minimum selector lies in the original domain
interval `(a,b)`. -/
theorem Ioo_subset_domain_of_subset_fiberMin_image {f : ℝ → ℝ} {a b u v c d : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite)
    (hdom : Set.Ioo u v ⊆ fiberMinDomain f a b)
    (hsub : Set.Ioo c d ⊆ fiberMin f a b hfin '' Set.Ioo u v) :
    Set.Ioo c d ⊆ Set.Ioo a b := by
  intro x hx
  rcases hsub hx with ⟨y, hy, rfl⟩
  exact (fiberMin_spec hfin (hdom hy)).1

/-- On any interval contained in the selector image, the original map is injective. -/
theorem injOn_of_subset_fiberMin_image {f : ℝ → ℝ} {a b u v c d : ℝ}
    (hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite)
    (hdom : Set.Ioo u v ⊆ fiberMinDomain f a b)
    (hsub : Set.Ioo c d ⊆ fiberMin f a b hfin '' Set.Ioo u v) :
    Set.InjOn f (Set.Ioo c d) := by
  intro x hx y hy hxy
  rcases hsub hx with ⟨sx, hsx, hsxEq⟩
  rcases hsub hy with ⟨sy, hsy, hsyEq⟩
  have hsxDom : sx ∈ fiberMinDomain f a b := hdom hsx
  have hsyDom : sy ∈ fiberMinDomain f a b := hdom hsy
  have hfx : f x = sx := by
    rw [← hsxEq]
    exact fiberMin_leftInverseOn hfin sx hsxDom
  have hfy : f y = sy := by
    rw [← hsyEq]
    exact fiberMin_leftInverseOn hfin sy hsyDom
  have hsxy : sx = sy := by
    calc
      sx = f x := hfx.symm
      _ = f y := hxy
      _ = sy := hfy
  calc
    x = fiberMin f a b hfin sx := hsxEq.symm
    _ = fiberMin f a b hfin sy := by rw [hsxy]
    _ = y := hsyEq

/-- Coste, Lemma 2.2, step 1: if `f` is not constant on any subinterval of `(a,b)`, then `f` is
injective on some smaller open subinterval. -/
theorem exists_injectiveOn_Ioo_of_no_const_subinterval
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hNoConst :
      ∀ u v : ℝ, Set.Ioo u v ⊆ Set.Ioo a b → u < v →
        ¬ Set.Subsingleton (f '' Set.Ioo u v)) :
    ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ Set.Ioo a b ∧ Set.InjOn f (Set.Ioo u v) := by
  let hfin : ∀ y : ℝ, (fiberEqOn f a b y).Finite :=
    fiber_finite_of_no_const_subinterval (S := S) (f := f) (a := a) (b := b) hf hNoConst
  rcases exists_Ioo_subset_image_of_no_const_subinterval
      (S := S) (f := f) (a := a) (b := b) hab hf hNoConst with
    ⟨u, v, huv, huvSub⟩
  rcases exists_Ioo_subset_fiberMin_image_of_Ioo_subset_domain
      (S := S) (f := f) (a := a) (b := b) (u := u) (v := v) hf hfin huv huvSub with
    ⟨c, d, hcd, hcdSub⟩
  refine ⟨c, d, hcd, ?_, ?_⟩
  · exact Ioo_subset_domain_of_subset_fiberMin_image hfin huvSub hcdSub
  · exact injOn_of_subset_fiberMin_image hfin huvSub hcdSub

/-- Local sign patterns in Coste's proof of Lemma 2.2. `plus` means “strictly above `f x`” and
`minus` means “strictly below `f x`”. -/
inductive LocalSign where
  | plus
  | minus
  deriving DecidableEq

/-- The order relation attached to a local sign pattern. -/
def LocalSign.Rel (σ : LocalSign) (f : ℝ → ℝ) (x y : ℝ) : Prop :=
  match σ with
  | .plus => f y > f x
  | .minus => f y < f x

@[simp] theorem localSignRel_plus {f : ℝ → ℝ} {x y : ℝ} :
    LocalSign.Rel .plus f x y ↔ f y > f x := Iff.rfl

@[simp] theorem localSignRel_minus {f : ℝ → ℝ} {x y : ℝ} :
    LocalSign.Rel .minus f x y ↔ f y < f x := Iff.rfl

/-- `LocPattern f a b l r x` says that near `x`, points on the left satisfy sign `l` relative to
`f x`, while points on the right satisfy sign `r`, all inside the ambient interval `(a,b)`. -/
def LocPattern (f : ℝ → ℝ) (a b : ℝ) (l r : LocalSign) (x : ℝ) : Prop :=
  ∃ ε > 0,
    Set.Ioo (x - ε) (x + ε) ⊆ Set.Ioo a b ∧
    (∀ y, x - ε < y → y < x → LocalSign.Rel l f x y) ∧
    (∀ y, x < y → y < x + ε → LocalSign.Rel r f x y)

/-- Points to the left of `x` on which the sign `σ` holds all the way up to `x`. -/
def leftSignSet (σ : LocalSign) (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ y < x ∧ ∀ z ∈ Set.Ico y x, LocalSign.Rel σ f x z}

/-- Points to the right of `x` on which the sign `σ` holds all the way from `x`. -/
def rightSignSet (σ : LocalSign) (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ x < y ∧ ∀ z ∈ Set.Ioc x y, LocalSign.Rel σ f x z}

@[simp] theorem mem_leftSignSet {σ : LocalSign} {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ leftSignSet σ f a b x ↔
      y ∈ Set.Ioo a b ∧ y < x ∧ ∀ z ∈ Set.Ico y x, LocalSign.Rel σ f x z := Iff.rfl

@[simp] theorem mem_rightSignSet {σ : LocalSign} {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ rightSignSet σ f a b x ↔
      y ∈ Set.Ioo a b ∧ x < y ∧ ∀ z ∈ Set.Ioc x y, LocalSign.Rel σ f x z := Iff.rfl

/-- Any local pattern yields a nonempty left one-sided interval witness. -/
theorem leftSignSet_nonempty_of_locPattern {f : ℝ → ℝ} {a b x : ℝ} {l r : LocalSign}
    (hpat : LocPattern f a b l r x) :
    (leftSignSet l f a b x).Nonempty := by
  rcases hpat with ⟨ε, hεpos, hsub, hleft, -⟩
  let y : ℝ := x - ε / 2
  have hy1 : x - ε < y := by
    dsimp [y]
    linarith
  have hy2 : y < x := by
    dsimp [y]
    linarith
  have hyI : y ∈ Set.Ioo a b := hsub ⟨hy1, by
    dsimp [y]
    linarith⟩
  refine ⟨y, hyI, hy2, ?_⟩
  intro z hz
  exact hleft z (lt_of_lt_of_le hy1 hz.1) hz.2

/-- Any local pattern yields a nonempty right one-sided interval witness. -/
theorem rightSignSet_nonempty_of_locPattern {f : ℝ → ℝ} {a b x : ℝ} {l r : LocalSign}
    (hpat : LocPattern f a b l r x) :
    (rightSignSet r f a b x).Nonempty := by
  rcases hpat with ⟨ε, hεpos, hsub, -, hright⟩
  let y : ℝ := x + ε / 2
  have hy1 : x < y := by
    dsimp [y]
    linarith
  have hy2 : y < x + ε := by
    dsimp [y]
    linarith
  have hyI : y ∈ Set.Ioo a b := hsub ⟨by
    dsimp [y]
    linarith, hy2⟩
  refine ⟨y, hyI, hy1, ?_⟩
  intro z hz
  exact hright z hz.1 (lt_of_le_of_lt hz.2 hy2)

/-- Conversely, nonempty left and right one-sided interval witnesses produce the corresponding
local pattern. -/
theorem locPattern_of_nonempty_leftSignSet_rightSignSet
    {f : ℝ → ℝ} {a b x : ℝ} {l r : LocalSign}
    (hleft : (leftSignSet l f a b x).Nonempty)
    (hright : (rightSignSet r f a b x).Nonempty) :
    LocPattern f a b l r x := by
  rcases hleft with ⟨u, huI, hux, hu⟩
  rcases hright with ⟨v, hvI, hxv, hv⟩
  let ε : ℝ := min (x - u) (v - x)
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min (sub_pos.mpr hux) (sub_pos.mpr hxv)
  have hεle_left : ε ≤ x - u := by
    dsimp [ε]
    exact min_le_left _ _
  have hεle_right : ε ≤ v - x := by
    dsimp [ε]
    exact min_le_right _ _
  refine ⟨ε, hεpos, ?_, ?_, ?_⟩
  · intro y hy
    constructor
    · have huy : u < y := by
        have : x - ε < y := hy.1
        linarith
      exact lt_trans huI.1 huy
    · have hyv : y < v := by
        have : y < x + ε := hy.2
        linarith
      exact lt_trans hyv hvI.2
  · intro y hy1 hy2
    have huy : u ≤ y := by
      have : x - ε < y := hy1
      linarith
    exact hu y ⟨huy, hy2⟩
  · intro y hy1 hy2
    have hyv : y ≤ v := by
      have : y < x + ε := hy2
      linarith
    exact hv y ⟨hy1, hyv⟩

/-- Local patterns are exactly the simultaneous nonemptiness of the corresponding one-sided
interval witness sets. -/
theorem locPattern_iff_nonempty_leftSignSet_rightSignSet
    {f : ℝ → ℝ} {a b x : ℝ} {l r : LocalSign} :
    LocPattern f a b l r x ↔
      (leftSignSet l f a b x).Nonempty ∧ (rightSignSet r f a b x).Nonempty := by
  constructor
  · intro hpat
    exact ⟨leftSignSet_nonempty_of_locPattern hpat, rightSignSet_nonempty_of_locPattern hpat⟩
  · rintro ⟨hleft, hright⟩
    exact locPattern_of_nonempty_leftSignSet_rightSignSet hleft hright

/-- Any local pattern occurs at a point of the ambient interval. -/
theorem mem_Ioo_of_locPattern {f : ℝ → ℝ} {a b x : ℝ} {l r : LocalSign}
    (hpat : LocPattern f a b l r x) :
    x ∈ Set.Ioo a b := by
  rcases hpat with ⟨ε, hεpos, hsub, -, -⟩
  exact hsub ⟨by linarith, by linarith⟩

/-- `Φ+,+` in Coste's notation. -/
abbrev locPattern_pp (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  LocPattern f a b .plus .plus x

/-- `Φ+,−` in Coste's notation. -/
abbrev locPattern_pm (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  LocPattern f a b .plus .minus x

/-- `Φ−,+` in Coste's notation. -/
abbrev locPattern_mp (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  LocPattern f a b .minus .plus x

/-- `Φ−,−` in Coste's notation. -/
abbrev locPattern_mm (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  LocPattern f a b .minus .minus x

/-- A local pattern can be shrunk to any smaller open interval containing the point. -/
theorem locPattern_restrict_Ioo
    {f : ℝ → ℝ} {a b u v x : ℝ} {l r : LocalSign}
    (hpat : LocPattern f a b l r x) (hx : x ∈ Set.Ioo u v) :
    LocPattern f u v l r x := by
  rcases hpat with ⟨ε, hεpos, -, hleft, hright⟩
  let δ : ℝ := min ε (min (x - u) (v - x))
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min hεpos ?_
    exact lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  have hδleε : δ ≤ ε := by
    dsimp [δ]
    exact min_le_left _ _
  have hδlexu : δ ≤ x - u := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδlevx : δ ≤ v - x := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, hδpos, ?_, ?_, ?_⟩
  · intro y hy
    constructor
    · have hyu : u < y := by
        have hy1 : x - δ < y := hy.1
        linarith
      exact hyu
    · have hyv : y < v := by
        have hy2 : y < x + δ := hy.2
        linarith
      exact hyv
  · intro y hy1 hy2
    exact hleft y (by linarith) hy2
  · intro y hy1 hy2
    exact hright y hy1 (by linarith)

/-- Coste's set `B`: points after which all later values are strictly above the current one. -/
def eventuallyAboveSet (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Ioo a b ∧ ∀ y ∈ Set.Ioo a b, x < y → f y > f x}

@[simp] theorem mem_eventuallyAboveSet {f : ℝ → ℝ} {a b x : ℝ} :
    x ∈ eventuallyAboveSet f a b ↔
      x ∈ Set.Ioo a b ∧ ∀ y ∈ Set.Ioo a b, x < y → f y > f x := Iff.rfl

/-- The leftward analogue of Coste's set `B`: points before which all earlier values are strictly
above the current one. -/
def eventuallyBelowSet (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Ioo a b ∧ ∀ y ∈ Set.Ioo a b, y < x → f y > f x}

@[simp] theorem mem_eventuallyBelowSet {f : ℝ → ℝ} {a b x : ℝ} :
    x ∈ eventuallyBelowSet f a b ↔
      x ∈ Set.Ioo a b ∧ ∀ y ∈ Set.Ioo a b, y < x → f y > f x := Iff.rfl

/-- Coste's set `C_x`: points to the right of `x` where the function drops below `f x`. -/
def dropRightSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ x < y ∧ f y < f x}

@[simp] theorem mem_dropRightSet {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ dropRightSet f a b x ↔ y ∈ Set.Ioo a b ∧ x < y ∧ f y < f x := Iff.rfl

/-- The leftward analogue of Coste's set `C_x`: points before `x` where the function drops below
`f x`. -/
def dropLeftSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ y < x ∧ f y < f x}

@[simp] theorem mem_dropLeftSet {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ dropLeftSet f a b x ↔ y ∈ Set.Ioo a b ∧ y < x ∧ f y < f x := Iff.rfl

/-- For a definable one-variable map, Coste's set `C_x` is definable. -/
theorem definable_dropRightSet {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (dropRightSet f a b x) := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let H : Set (Rn 2) :=
    rawProdSet 1 1 (encodeSet ℝ (Set.Ioi x)) (encodeSet ℝ (Set.Iio (f x)))
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hH : S.Definable H := by
    dsimp [H]
    exact S.definable_prod
      (by simpa [DefinableSetOf] using S.definableIoi x)
      (by simpa [DefinableSetOf] using S.definableIio (f x))
  have hProj : S.Definable (prefixProjection 1 1 (G ∩ H)) :=
    S.definable_projection (S.definable_inter hG hH)
  have hEq : prefixProjection 1 1 (G ∩ H) = encodeSet ℝ (dropRightSet f a b x) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨w, hw⟩
      have hwG : Fin.append y w ∈ G := hw.1
      have hwH : Fin.append y w ∈ H := hw.2
      have hyGraph : rn1ToScalar y ∈ Set.Ioo a b ∧ rn1ToScalar w = f (rn1ToScalar y) := by
        simpa [G, rawGraph] using hwG
      have hyCut : rn1ToScalar y ∈ Set.Ioi x ∧ rn1ToScalar w ∈ Set.Iio (f x) := by
        have hwH' :
            Fin.append y w ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioi x)) (encodeSet ℝ (Set.Iio (f x))) := by
          simpa [H] using hwH
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real] at hwH'
        simpa using hwH'
      have hyDrop : rn1ToScalar y ∈ dropRightSet f a b x := by
        refine ⟨hyGraph.1, hyCut.1, ?_⟩
        simpa [hyGraph.2] using hyCut.2
      simpa [mem_encodeSet_real] using hyDrop
    · intro hy
      have hyDrop : rn1ToScalar y ∈ dropRightSet f a b x := by
        simpa [mem_encodeSet_real] using hy
      refine ⟨scalarToRn1 (f (rn1ToScalar y)), ?_⟩
      have hGraph :
          Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈ G := by
        have hgraph' : (rn1ToScalar y, f (rn1ToScalar y)) ∈ rawGraph (Set.Ioo a b) f := by
          exact ⟨hyDrop.1, rfl⟩
        simpa [G] using hgraph'
      have hCut :
          Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈ H := by
        have hCut' :
            Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioi x)) (encodeSet ℝ (Set.Iio (f x))) := by
          rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real]
          exact ⟨hyDrop.2.1, by simpa [rn1ToScalar_scalarToRn1] using hyDrop.2.2⟩
        simpa [H] using hCut'
      exact ⟨hGraph, hCut⟩
  simpa [hEq] using hProj

/-- For a definable one-variable map, the leftward drop set is definable. -/
theorem definable_dropLeftSet {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (dropLeftSet f a b x) := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let H : Set (Rn 2) :=
    rawProdSet 1 1 (encodeSet ℝ (Set.Iio x)) (encodeSet ℝ (Set.Iio (f x)))
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hH : S.Definable H := by
    dsimp [H]
    exact S.definable_prod
      (by simpa [DefinableSetOf] using S.definableIio x)
      (by simpa [DefinableSetOf] using S.definableIio (f x))
  have hProj : S.Definable (prefixProjection 1 1 (G ∩ H)) :=
    S.definable_projection (S.definable_inter hG hH)
  have hEq : prefixProjection 1 1 (G ∩ H) = encodeSet ℝ (dropLeftSet f a b x) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨w, hw⟩
      have hwG : Fin.append y w ∈ G := hw.1
      have hwH : Fin.append y w ∈ H := hw.2
      have hyGraph : rn1ToScalar y ∈ Set.Ioo a b ∧ rn1ToScalar w = f (rn1ToScalar y) := by
        simpa [G, rawGraph] using hwG
      have hyCut : rn1ToScalar y ∈ Set.Iio x ∧ rn1ToScalar w ∈ Set.Iio (f x) := by
        have hwH' :
            Fin.append y w ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Iio x)) (encodeSet ℝ (Set.Iio (f x))) := by
          simpa [H] using hwH
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real] at hwH'
        simpa using hwH'
      have hyDrop : rn1ToScalar y ∈ dropLeftSet f a b x := by
        refine ⟨hyGraph.1, hyCut.1, ?_⟩
        simpa [hyGraph.2] using hyCut.2
      simpa [mem_encodeSet_real] using hyDrop
    · intro hy
      have hyDrop : rn1ToScalar y ∈ dropLeftSet f a b x := by
        simpa [mem_encodeSet_real] using hy
      refine ⟨scalarToRn1 (f (rn1ToScalar y)), ?_⟩
      have hGraph :
          Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈ G := by
        have hgraph' : (rn1ToScalar y, f (rn1ToScalar y)) ∈ rawGraph (Set.Ioo a b) f := by
          exact ⟨hyDrop.1, rfl⟩
        simpa [G] using hgraph'
      have hCut :
          Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈ H := by
        have hCut' :
            Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Iio x)) (encodeSet ℝ (Set.Iio (f x))) := by
          rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real]
          exact ⟨hyDrop.2.1, by simpa [rn1ToScalar_scalarToRn1] using hyDrop.2.2⟩
        simpa [H] using hCut'
      exact ⟨hGraph, hCut⟩
  simpa [hEq] using hProj

/-- Points to the right of `x` where `f` does not rise strictly above `f x`. -/
def nonRiseFromSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ x < y ∧ ¬ f x < f y}

@[simp] theorem mem_nonRiseFromSet {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ nonRiseFromSet f a b x ↔ y ∈ Set.Ioo a b ∧ x < y ∧ ¬ f x < f y := Iff.rfl

/-- For a definable one-variable map, the right-hand non-rise set from `x` is definable. -/
theorem definable_nonRiseFromSet {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (nonRiseFromSet f a b x) := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let H : Set (Rn 2) :=
    rawProdSet 1 1 (encodeSet ℝ (Set.Ioi x)) ((encodeSet ℝ (Set.Ioi (f x)))ᶜ)
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hH : S.Definable H := by
    dsimp [H]
    exact S.definable_prod
      (by simpa [DefinableSetOf] using S.definableIoi x)
      (S.definable_compl (by simpa [DefinableSetOf] using S.definableIoi (f x)))
  have hProj : S.Definable (prefixProjection 1 1 (G ∩ H)) :=
    S.definable_projection (S.definable_inter hG hH)
  have hEq : prefixProjection 1 1 (G ∩ H) = encodeSet ℝ (nonRiseFromSet f a b x) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨w, hw⟩
      have hwG : Fin.append y w ∈ G := hw.1
      have hwH : Fin.append y w ∈ H := hw.2
      have hyGraph : rn1ToScalar y ∈ Set.Ioo a b ∧ rn1ToScalar w = f (rn1ToScalar y) := by
        simpa [G, rawGraph] using hwG
      have hyCut : rn1ToScalar y ∈ Set.Ioi x ∧ rn1ToScalar w ∉ Set.Ioi (f x) := by
        have hwH' :
            Fin.append y w ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioi x)) ((encodeSet ℝ (Set.Ioi (f x)))ᶜ) := by
          simpa [H] using hwH
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_compl_iff,
          mem_encodeSet_real] at hwH'
        simpa using hwH'
      have hyNonRise : rn1ToScalar y ∈ nonRiseFromSet f a b x := by
        refine ⟨hyGraph.1, hyCut.1, ?_⟩
        simpa [hyGraph.2] using hyCut.2
      change rn1ToScalar y ∈ nonRiseFromSet f a b x
      exact hyNonRise
    · intro hy
      have hyNonRise : rn1ToScalar y ∈ nonRiseFromSet f a b x := by
        change rn1ToScalar y ∈ nonRiseFromSet f a b x at hy
        exact hy
      refine ⟨scalarToRn1 (f (rn1ToScalar y)), ?_⟩
      have hGraph :
          Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈ G := by
        have hgraph' : (rn1ToScalar y, f (rn1ToScalar y)) ∈ rawGraph (Set.Ioo a b) f := by
          exact ⟨hyNonRise.1, rfl⟩
        simpa [G] using hgraph'
      have hCut :
          Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈ H := by
        have hCut' :
            Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioi x)) ((encodeSet ℝ (Set.Ioi (f x)))ᶜ) := by
          rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_compl_iff,
            mem_encodeSet_real]
          exact ⟨hyNonRise.2.1, by simpa [rn1ToScalar_scalarToRn1] using hyNonRise.2.2⟩
        simpa [H] using hCut'
      exact ⟨hGraph, hCut⟩
  simpa [hEq] using hProj

/-- Points to the left of `x` where `f` does not rise strictly above `f x`. -/
def nonRiseToSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ y < x ∧ ¬ f x < f y}

@[simp] theorem mem_nonRiseToSet {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ nonRiseToSet f a b x ↔ y ∈ Set.Ioo a b ∧ y < x ∧ ¬ f x < f y := Iff.rfl

/-- For a definable one-variable map, the left-hand non-rise set toward `x` is definable. -/
theorem definable_nonRiseToSet {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (nonRiseToSet f a b x) := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let H : Set (Rn 2) :=
    rawProdSet 1 1 (encodeSet ℝ (Set.Iio x)) ((encodeSet ℝ (Set.Ioi (f x)))ᶜ)
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hH : S.Definable H := by
    dsimp [H]
    exact S.definable_prod
      (by simpa [DefinableSetOf] using S.definableIio x)
      (S.definable_compl (by simpa [DefinableSetOf] using S.definableIoi (f x)))
  have hProj : S.Definable (prefixProjection 1 1 (G ∩ H)) :=
    S.definable_projection (S.definable_inter hG hH)
  have hEq : prefixProjection 1 1 (G ∩ H) = encodeSet ℝ (nonRiseToSet f a b x) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨w, hw⟩
      have hwG : Fin.append y w ∈ G := hw.1
      have hwH : Fin.append y w ∈ H := hw.2
      have hyGraph : rn1ToScalar y ∈ Set.Ioo a b ∧ rn1ToScalar w = f (rn1ToScalar y) := by
        simpa [G, rawGraph] using hwG
      have hyCut : rn1ToScalar y ∈ Set.Iio x ∧ rn1ToScalar w ∉ Set.Ioi (f x) := by
        have hwH' :
            Fin.append y w ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Iio x)) ((encodeSet ℝ (Set.Ioi (f x)))ᶜ) := by
          simpa [H] using hwH
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_compl_iff,
          mem_encodeSet_real] at hwH'
        simpa using hwH'
      have hyNonRise : rn1ToScalar y ∈ nonRiseToSet f a b x := by
        refine ⟨hyGraph.1, hyCut.1, ?_⟩
        simpa [hyGraph.2] using hyCut.2
      change rn1ToScalar y ∈ nonRiseToSet f a b x
      exact hyNonRise
    · intro hy
      have hyNonRise : rn1ToScalar y ∈ nonRiseToSet f a b x := by
        change rn1ToScalar y ∈ nonRiseToSet f a b x at hy
        exact hy
      refine ⟨scalarToRn1 (f (rn1ToScalar y)), ?_⟩
      have hGraph :
          Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈ G := by
        have hgraph' : (rn1ToScalar y, f (rn1ToScalar y)) ∈ rawGraph (Set.Ioo a b) f := by
          exact ⟨hyNonRise.1, rfl⟩
        simpa [G] using hgraph'
      have hCut :
          Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈ H := by
        have hCut' :
            Fin.append y (scalarToRn1 (f (rn1ToScalar y))) ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Iio x)) ((encodeSet ℝ (Set.Ioi (f x)))ᶜ) := by
          rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_compl_iff,
            mem_encodeSet_real]
          exact ⟨hyNonRise.2.1, by simpa [rn1ToScalar_scalarToRn1] using hyNonRise.2.2⟩
        simpa [H] using hCut'
      exact ⟨hGraph, hCut⟩
  simpa [hEq] using hProj

/-- The bad right-above set: points `y` for which some non-rise witness from `x` already occurs
at or before `y`. -/
def badRightAboveSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ ∃ z ∈ nonRiseFromSet f a b x, z ≤ y}

@[simp] theorem mem_badRightAboveSet {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ badRightAboveSet f a b x ↔ y ∈ Set.Ioo a b ∧ ∃ z ∈ nonRiseFromSet f a b x, z ≤ y :=
  Iff.rfl

/-- The bad right-above set is definable. -/
theorem definable_badRightAboveSet {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (badRightAboveSet f a b x) := by
  let P : Set (Rn 2) :=
    rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (nonRiseFromSet f a b x))
  let LtYZ : Set (Rn 2) := encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}
  have hNR : S.Definable (encodeSet ℝ (nonRiseFromSet f a b x)) := by
    simpa [DefinableSetOf] using
      (definable_nonRiseFromSet (S := S) (f := f) (a := a) (b := b) (x := x) hf)
  have hP : S.Definable P := by
    dsimp [P]
    exact S.definable_prod
      (by simpa [DefinableSetOf] using S.definableIoo a b)
      hNR
  have hLtYZ : S.Definable LtYZ := by
    simpa [DefinableSetOf] using S.definableLt
  have hProj : S.Definable (prefixProjection 1 1 (P ∩ LtYZᶜ)) :=
    S.definable_projection (S.definable_inter hP (S.definable_compl hLtYZ))
  have hEq : prefixProjection 1 1 (P ∩ LtYZᶜ) = encodeSet ℝ (badRightAboveSet f a b x) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz⟩
      have hzP : Fin.append y z ∈ P := hz.1
      have hzLt : Fin.append y z ∉ LtYZ := hz.2
      have hyI : rn1ToScalar y ∈ Set.Ioo a b := by
        have hzP' :
            Fin.append y z ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (nonRiseFromSet f a b x)) := by
          simpa [P] using hzP
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real] at hzP'
        exact hzP'.1
      have hzNonRise : rn1ToScalar z ∈ nonRiseFromSet f a b x := by
        have hzP' :
            Fin.append y z ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (nonRiseFromSet f a b x)) := by
          simpa [P] using hzP
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real] at hzP'
        exact hzP'.2
      have hyz_notlt : ¬ rn1ToScalar y < rn1ToScalar z := by
        change Fin.append y z ∉ encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2} at hzLt
        simpa [mem_encodeSet_real_prod] using hzLt
      have hyBad : rn1ToScalar y ∈ badRightAboveSet f a b x := by
        refine ⟨hyI, rn1ToScalar z, hzNonRise, le_of_not_gt hyz_notlt⟩
      change rn1ToScalar y ∈ badRightAboveSet f a b x
      exact hyBad
    · intro hy
      have hyBad : rn1ToScalar y ∈ badRightAboveSet f a b x := by
        change rn1ToScalar y ∈ badRightAboveSet f a b x at hy
        exact hy
      rcases hyBad with ⟨hyI, z, hzNonRise, hzy⟩
      refine ⟨scalarToRn1 z, ?_⟩
      have hPmem : Fin.append y (scalarToRn1 z) ∈ P := by
        have hPmem' :
            Fin.append y (scalarToRn1 z) ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (nonRiseFromSet f a b x)) := by
          rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real]
          exact ⟨hyI, by simpa [rn1ToScalar_scalarToRn1] using hzNonRise⟩
        simpa [P] using hPmem'
      have hLtmem : Fin.append y (scalarToRn1 z) ∈ LtYZᶜ := by
        change Fin.append y (scalarToRn1 z) ∉ encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}
        simpa [mem_encodeSet_real_prod, rn1ToScalar_scalarToRn1] using not_lt_of_ge hzy
      exact ⟨hPmem, hLtmem⟩
  simpa [hEq] using hProj

/-- The bad left-above set: points `y` for which some non-rise witness before `x` already occurs
at or to the right of `y`. -/
def badLeftAboveSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ ∃ z ∈ nonRiseToSet f a b x, y ≤ z}

@[simp] theorem mem_badLeftAboveSet {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ badLeftAboveSet f a b x ↔ y ∈ Set.Ioo a b ∧ ∃ z ∈ nonRiseToSet f a b x, y ≤ z :=
  Iff.rfl

/-- The bad left-above set is definable. -/
theorem definable_badLeftAboveSet {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (badLeftAboveSet f a b x) := by
  let P : Set (Rn 2) :=
    rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (nonRiseToSet f a b x))
  let LtZY : Set (Rn 2) :=
    reindexSet swapFin2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  have hNR : S.Definable (encodeSet ℝ (nonRiseToSet f a b x)) := by
    simpa [DefinableSetOf] using
      (definable_nonRiseToSet (S := S) (f := f) (a := a) (b := b) (x := x) hf)
  have hP : S.Definable P := by
    dsimp [P]
    exact S.definable_prod
      (by simpa [DefinableSetOf] using S.definableIoo a b)
      hNR
  have hLtZY : S.Definable LtZY := by
    dsimp [LtZY]
    exact S.definableReindex swapFin2 (by simpa [DefinableSetOf] using S.definableLt)
  have hProj : S.Definable (prefixProjection 1 1 (P ∩ LtZYᶜ)) :=
    S.definable_projection (S.definable_inter hP (S.definable_compl hLtZY))
  have hEq : prefixProjection 1 1 (P ∩ LtZYᶜ) = encodeSet ℝ (badLeftAboveSet f a b x) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz⟩
      have hzP : Fin.append y z ∈ P := hz.1
      have hzLt : Fin.append y z ∉ LtZY := hz.2
      have hyI : rn1ToScalar y ∈ Set.Ioo a b := by
        have hzP' :
            Fin.append y z ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (nonRiseToSet f a b x)) := by
          simpa [P] using hzP
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real] at hzP'
        exact hzP'.1
      have hzNonRise : rn1ToScalar z ∈ nonRiseToSet f a b x := by
        have hzP' :
            Fin.append y z ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (nonRiseToSet f a b x)) := by
          simpa [P] using hzP
        rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real] at hzP'
        exact hzP'.2
      have hzy_notlt : ¬ rn1ToScalar z < rn1ToScalar y := by
        change Fin.append y z ∉ reindexSet swapFin2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) at hzLt
        rw [mem_reindexSet, reindexRn_swapFin2_fin_append, mem_encodeSet_real_prod] at hzLt
        simpa using hzLt
      have hyBad : rn1ToScalar y ∈ badLeftAboveSet f a b x := by
        refine ⟨hyI, rn1ToScalar z, hzNonRise, le_of_not_gt hzy_notlt⟩
      change rn1ToScalar y ∈ badLeftAboveSet f a b x
      exact hyBad
    · intro hy
      have hyBad : rn1ToScalar y ∈ badLeftAboveSet f a b x := by
        change rn1ToScalar y ∈ badLeftAboveSet f a b x at hy
        exact hy
      rcases hyBad with ⟨hyI, z, hzNonRise, hyz⟩
      refine ⟨scalarToRn1 z, ?_⟩
      have hPmem : Fin.append y (scalarToRn1 z) ∈ P := by
        have hPmem' :
            Fin.append y (scalarToRn1 z) ∈
              rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (nonRiseToSet f a b x)) := by
          rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real, mem_encodeSet_real]
          exact ⟨hyI, by simpa [rn1ToScalar_scalarToRn1] using hzNonRise⟩
        simpa [P] using hPmem'
      have hLtmem : Fin.append y (scalarToRn1 z) ∈ LtZYᶜ := by
        change Fin.append y (scalarToRn1 z) ∉
          reindexSet swapFin2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
        rw [mem_reindexSet, reindexRn_swapFin2_fin_append, mem_encodeSet_real_prod]
        simpa [rn1ToScalar_scalarToRn1] using not_lt_of_ge hyz
      exact ⟨hPmem, hLtmem⟩
  simpa [hEq] using hProj

/-- If Coste's set `C_x` is infinite, o-minimality shrinks it to a nontrivial open interval. -/
theorem exists_Ioo_subset_dropRightSet_of_infinite {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hInf : (dropRightSet f a b x).Infinite) :
    ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ dropRightSet f a b x :=
  definable_infinite_subset_real_contains_Ioo (S := S)
    (definable_dropRightSet (S := S) (f := f) (a := a) (b := b) (x := x) hf) hInf

/-- If the leftward drop set is infinite, o-minimality shrinks it to a nontrivial open interval. -/
theorem exists_Ioo_subset_dropLeftSet_of_infinite {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hInf : (dropLeftSet f a b x).Infinite) :
    ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ dropLeftSet f a b x :=
  definable_infinite_subset_real_contains_Ioo (S := S)
    (definable_dropLeftSet (S := S) (f := f) (a := a) (b := b) (x := x) hf) hInf

/-- A witness-based version of the interior of Coste's set `C_x`: points lying in some open
interval contained in `C_x`. -/
def dropRightInteriorSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {z : ℝ | ∃ u v : ℝ, u < v ∧ z ∈ Set.Ioo u v ∧ Set.Ioo u v ⊆ dropRightSet f a b x}

@[simp] theorem mem_dropRightInteriorSet {f : ℝ → ℝ} {a b x z : ℝ} :
    z ∈ dropRightInteriorSet f a b x ↔
      ∃ u v : ℝ, u < v ∧ z ∈ Set.Ioo u v ∧ Set.Ioo u v ⊆ dropRightSet f a b x := Iff.rfl

/-- Every point of the witness-based interior of `C_x` already lies in `C_x`. -/
theorem mem_dropRightSet_of_mem_dropRightInteriorSet {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropRightInteriorSet f a b x) :
    z ∈ dropRightSet f a b x := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  exact hsub hzuv

/-- The witness-based interior of `C_x` is nonempty as soon as `C_x` contains an open interval. -/
theorem dropRightInteriorSet_nonempty_of_exists_Ioo_subset
    {f : ℝ → ℝ} {a b x u v : ℝ}
    (huv : u < v) (hsub : Set.Ioo u v ⊆ dropRightSet f a b x) :
    (dropRightInteriorSet f a b x).Nonempty := by
  let z : ℝ := (u + v) / 2
  have hzuv : z ∈ Set.Ioo u v := by
    dsimp [z]
    constructor <;> linarith
  exact ⟨z, u, v, huv, hzuv, hsub⟩

/-- Every point of the witness-based interior of `C_x` lies strictly to the right of `x`. -/
theorem x_lt_of_mem_dropRightInteriorSet {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropRightInteriorSet f a b x) :
    x < z :=
  (mem_dropRightSet_of_mem_dropRightInteriorSet hz).2.1

/-- Every point of the witness-based interior of `C_x` lies in the ambient interval `(a,b)`. -/
theorem mem_Ioo_of_mem_dropRightInteriorSet {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropRightInteriorSet f a b x) :
    z ∈ Set.Ioo a b :=
  (mem_dropRightSet_of_mem_dropRightInteriorSet hz).1

/-- Any interior point of `C_x` carries a left subinterval of `C_x` ending at that point. -/
theorem exists_Ioo_subset_dropRightSet_left_of_mem_dropRightInteriorSet
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropRightInteriorSet f a b x) :
    ∃ u : ℝ, u < z ∧ Set.Ioo u z ⊆ dropRightSet f a b x := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  let w : ℝ := (u + z) / 2
  have huw : u < w := by
    dsimp [w]
    linarith [hzuv.1]
  have hwz : w < z := by
    dsimp [w]
    linarith [hzuv.1]
  refine ⟨w, hwz, ?_⟩
  intro t ht
  exact hsub ⟨lt_trans huw ht.1, lt_trans ht.2 hzuv.2⟩

/-- Any interior point of `C_x` carries a right subinterval of `C_x` starting at that point. -/
theorem exists_Ioo_subset_dropRightSet_right_of_mem_dropRightInteriorSet
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropRightInteriorSet f a b x) :
    ∃ v : ℝ, z < v ∧ Set.Ioo z v ⊆ dropRightSet f a b x := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  let w : ℝ := (z + v) / 2
  have hzw : z < w := by
    dsimp [w]
    linarith [hzuv.2]
  have hwv : w < v := by
    dsimp [w]
    linarith [hzuv.2]
  refine ⟨w, hzw, ?_⟩
  intro t ht
  exact hsub ⟨lt_trans hzuv.1 ht.1, lt_trans ht.2 hwv⟩

/-- The witness-based interior of `C_x` is open, in the explicit interval-neighborhood form. -/
theorem exists_small_Ioo_subset_dropRightInteriorSet_of_mem
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropRightInteriorSet f a b x) :
    ∃ ε > 0, Set.Ioo (z - ε) (z + ε) ⊆ dropRightInteriorSet f a b x := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  rcases exists_small_Ioo_around_mem_Ioo (a := u) (b := v) (x := z) hzuv with
    ⟨ε, hεpos, hεsub⟩
  refine ⟨ε, hεpos, ?_⟩
  intro t ht
  exact ⟨u, v, huv, hεsub ht, hsub⟩

/-- The witness-based interior of `C_x` is an open subset of `ℝ`. -/
theorem isOpen_dropRightInteriorSet {f : ℝ → ℝ} {a b x : ℝ} :
    IsOpen (dropRightInteriorSet f a b x) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases exists_small_Ioo_subset_dropRightInteriorSet_of_mem hz with ⟨ε, hεpos, hεsub⟩
  have hzI : z ∈ Set.Ioo (z - ε) (z + ε) := by
    constructor <;> linarith
  exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hzI) hεsub

/-- The witness-based interior of `C_x` is bounded below by `x`. -/
theorem bddBelow_dropRightInteriorSet {f : ℝ → ℝ} {a b x : ℝ} :
    BddBelow (dropRightInteriorSet f a b x) := by
  refine ⟨x, ?_⟩
  intro z hz
  exact (x_lt_of_mem_dropRightInteriorSet hz).le

/-- A witness-based version of the interior of the leftward drop set. -/
def dropLeftInteriorSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {z : ℝ | ∃ u v : ℝ, u < v ∧ z ∈ Set.Ioo u v ∧ Set.Ioo u v ⊆ dropLeftSet f a b x}

@[simp] theorem mem_dropLeftInteriorSet {f : ℝ → ℝ} {a b x z : ℝ} :
    z ∈ dropLeftInteriorSet f a b x ↔
      ∃ u v : ℝ, u < v ∧ z ∈ Set.Ioo u v ∧ Set.Ioo u v ⊆ dropLeftSet f a b x := Iff.rfl

/-- Every point of the witness-based interior of the leftward drop set already lies in it. -/
theorem mem_dropLeftSet_of_mem_dropLeftInteriorSet {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropLeftInteriorSet f a b x) :
    z ∈ dropLeftSet f a b x := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  exact hsub hzuv

/-- The witness-based interior of the leftward drop set is nonempty as soon as the set contains
an open interval. -/
theorem dropLeftInteriorSet_nonempty_of_exists_Ioo_subset
    {f : ℝ → ℝ} {a b x u v : ℝ}
    (huv : u < v) (hsub : Set.Ioo u v ⊆ dropLeftSet f a b x) :
    (dropLeftInteriorSet f a b x).Nonempty := by
  let z : ℝ := (u + v) / 2
  have hzuv : z ∈ Set.Ioo u v := by
    dsimp [z]
    constructor <;> linarith
  exact ⟨z, u, v, huv, hzuv, hsub⟩

/-- Every point of the witness-based interior of the leftward drop set lies strictly to the left
of `x`. -/
theorem lt_x_of_mem_dropLeftInteriorSet {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropLeftInteriorSet f a b x) :
    z < x :=
  (mem_dropLeftSet_of_mem_dropLeftInteriorSet hz).2.1

/-- Every point of the witness-based interior of the leftward drop set lies in `(a,b)`. -/
theorem mem_Ioo_of_mem_dropLeftInteriorSet {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropLeftInteriorSet f a b x) :
    z ∈ Set.Ioo a b :=
  (mem_dropLeftSet_of_mem_dropLeftInteriorSet hz).1

/-- Any interior point of the leftward drop set carries a left subinterval contained in that set. -/
theorem exists_Ioo_subset_dropLeftSet_left_of_mem_dropLeftInteriorSet
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropLeftInteriorSet f a b x) :
    ∃ u : ℝ, u < z ∧ Set.Ioo u z ⊆ dropLeftSet f a b x := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  let w : ℝ := (u + z) / 2
  have huw : u < w := by
    dsimp [w]
    linarith [hzuv.1]
  have hwz : w < z := by
    dsimp [w]
    linarith [hzuv.1]
  refine ⟨w, hwz, ?_⟩
  intro t ht
  exact hsub ⟨lt_trans huw ht.1, lt_trans ht.2 hzuv.2⟩

/-- Any interior point of the leftward drop set carries a right subinterval contained in that
set. -/
theorem exists_Ioo_subset_dropLeftSet_right_of_mem_dropLeftInteriorSet
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropLeftInteriorSet f a b x) :
    ∃ v : ℝ, z < v ∧ Set.Ioo z v ⊆ dropLeftSet f a b x := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  let w : ℝ := (z + v) / 2
  have hzw : z < w := by
    dsimp [w]
    linarith [hzuv.2]
  have hwv : w < v := by
    dsimp [w]
    linarith [hzuv.2]
  refine ⟨w, hzw, ?_⟩
  intro t ht
  exact hsub ⟨lt_trans hzuv.1 ht.1, lt_trans ht.2 hwv⟩

/-- The witness-based interior of the leftward drop set is open, in explicit interval-neighborhood
form. -/
theorem exists_small_Ioo_subset_dropLeftInteriorSet_of_mem
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hz : z ∈ dropLeftInteriorSet f a b x) :
    ∃ ε > 0, Set.Ioo (z - ε) (z + ε) ⊆ dropLeftInteriorSet f a b x := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  rcases exists_small_Ioo_around_mem_Ioo (a := u) (b := v) (x := z) hzuv with
    ⟨ε, hεpos, hεsub⟩
  refine ⟨ε, hεpos, ?_⟩
  intro t ht
  exact ⟨u, v, huv, hεsub ht, hsub⟩

/-- The witness-based interior of the leftward drop set is open. -/
theorem isOpen_dropLeftInteriorSet {f : ℝ → ℝ} {a b x : ℝ} :
    IsOpen (dropLeftInteriorSet f a b x) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases exists_small_Ioo_subset_dropLeftInteriorSet_of_mem hz with ⟨ε, hεpos, hεsub⟩
  have hzI : z ∈ Set.Ioo (z - ε) (z + ε) := by
    constructor <;> linarith
  exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hzI) hεsub

/-- The witness-based interior of the leftward drop set is bounded above by `x`. -/
theorem bddAbove_dropLeftInteriorSet {f : ℝ → ℝ} {a b x : ℝ} :
    BddAbove (dropLeftInteriorSet f a b x) := by
  refine ⟨x, ?_⟩
  intro z hz
  exact (lt_x_of_mem_dropLeftInteriorSet hz).le

/-- Raw quadruples `(x, y, f x, f y)` with `x < y` and `f y ≤ f x`. -/
def nonRiseWitnessSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 4) :=
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let GG : Set (Rn 4) := reindexSet swapFin4Mid (rawProdSet 2 2 G G)
  let LtXY : Set (Rn 4) :=
    rawProdSet 2 2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) (Set.univ : Set (Rn 2))
  let LtVals : Set (Rn 4) :=
    rawProdSet 2 2 (Set.univ : Set (Rn 2))
      (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  GG ∩ LtXY ∩ LtValsᶜ

/-- The raw non-rise witness set is definable. -/
theorem definable_nonRiseWitnessSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (nonRiseWitnessSet f a b) := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let GG : Set (Rn 4) := reindexSet swapFin4Mid (rawProdSet 2 2 G G)
  let LtXY : Set (Rn 4) :=
    rawProdSet 2 2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) (Set.univ : Set (Rn 2))
  let LtVals : Set (Rn 4) :=
    rawProdSet 2 2 (Set.univ : Set (Rn 2))
      (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hLt : S.Definable (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) := by
    simpa [DefinableSetOf] using S.definableLt
  have hGG : S.Definable GG := by
    dsimp [GG]
    exact S.definableReindex swapFin4Mid (S.definable_prod hG hG)
  have hLtXY : S.Definable LtXY := by
    dsimp [LtXY]
    exact S.definable_prod hLt S.definable_univ
  have hLtVals : S.Definable LtVals := by
    dsimp [LtVals]
    exact S.definable_prod S.definable_univ hLt
  dsimp [nonRiseWitnessSet, G, GG, LtXY, LtVals]
  exact S.definable_inter (S.definable_inter hGG hLtXY) (S.definable_compl hLtVals)

@[simp] theorem fin_append_append_mem_nonRiseWitnessSet
    {f : ℝ → ℝ} {a b : ℝ} {x y fx fy : Rn 1} :
    Fin.append (Fin.append x y) (Fin.append fx fy) ∈ nonRiseWitnessSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar y ∈ Set.Ioo a b ∧
      rn1ToScalar fx = f (rn1ToScalar x) ∧
      rn1ToScalar fy = f (rn1ToScalar y) ∧
      rn1ToScalar x < rn1ToScalar y ∧
      ¬ rn1ToScalar fx < rn1ToScalar fy := by
  dsimp [nonRiseWitnessSet]
  rw [mem_inter_iff, mem_inter_iff]
  rw [mem_reindexSet, reindexRn_swapFin4Mid_quad]
  rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real_prod, splitAtEquiv_fin_append,
    mem_encodeSet_real_prod, splitAtEquiv_fin_append]
  rw [mem_rawProdSet, splitAtEquiv_fin_append, fin_append_mem_ltPairSet]
  rw [mem_compl_iff, mem_rawProdSet, splitAtEquiv_fin_append, fin_append_mem_ltPairSet]
  simp [rawGraph, and_assoc, and_left_comm, and_comm]

/-- Raw pairs `(x, y)` with `x < y` and `f y ≤ f x`. -/
def nonRisePairSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  prefixProjection 2 2 (nonRiseWitnessSet f a b)

/-- The raw non-rise pair set is definable. -/
theorem definable_nonRisePairSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (nonRisePairSet f a b) :=
  S.definable_projection (definable_nonRiseWitnessSet (S := S) (f := f) (a := a) (b := b) hf)

@[simp] theorem fin_append_mem_nonRisePairSet
    {f : ℝ → ℝ} {a b : ℝ} {x y : Rn 1} :
    Fin.append x y ∈ nonRisePairSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar y ∈ Set.Ioo a b ∧
      rn1ToScalar x < rn1ToScalar y ∧
      ¬ f (rn1ToScalar x) < f (rn1ToScalar y) := by
  constructor
  · intro hxy
    rcases hxy with ⟨z, hz⟩
    let fx : Rn 1 := (splitAtEquiv 1 1 z).1
    let fy : Rn 1 := (splitAtEquiv 1 1 z).2
    have hzEq : z = Fin.append fx fy := by
      have hz0 : z = (splitAtEquiv 1 1).symm (((splitAtEquiv 1 1) z).1, ((splitAtEquiv 1 1) z).2) := by
        simpa using (Equiv.symm_apply_apply (splitAtEquiv 1 1) z).symm
      have hz1 :
          (splitAtEquiv 1 1).symm (((splitAtEquiv 1 1) z).1, ((splitAtEquiv 1 1) z).2) =
            Fin.append fx fy := by
        simpa [fx, fy] using
          (splitAtEquiv_symm_apply (((splitAtEquiv 1 1) z).1) (((splitAtEquiv 1 1) z).2))
      exact hz0.trans hz1
    rw [hzEq] at hz
    rcases (fin_append_append_mem_nonRiseWitnessSet (x := x) (y := y) (fx := fx) (fy := fy)).mp hz
      with ⟨hxIoo, hyIoo, hfx, hfy, hxylt, hnotlt⟩
    simpa [fx, fy] using ⟨hxIoo, hyIoo, hxylt, by simpa [hfx, hfy] using hnotlt⟩
  · rintro ⟨hxIoo, hyIoo, hxylt, hnotlt⟩
    refine ⟨Fin.append (scalarToRn1 (f (rn1ToScalar x))) (scalarToRn1 (f (rn1ToScalar y))), ?_⟩
    simpa [rn1ToScalar_scalarToRn1] using
      (fin_append_append_mem_nonRiseWitnessSet
        (x := x) (y := y)
        (fx := scalarToRn1 (f (rn1ToScalar x)))
        (fy := scalarToRn1 (f (rn1ToScalar y)))).2
        ⟨hxIoo, hyIoo, rfl, rfl, hxylt, by simpa [rn1ToScalar_scalarToRn1] using hnotlt⟩

/-- Raw quadruples `(x, y, f x, f y)` with `y < x` and `f y ≤ f x`. -/
def nonRiseToWitnessSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 4) :=
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let GG : Set (Rn 4) := reindexSet swapFin4Mid (rawProdSet 2 2 G G)
  let GtXY : Set (Rn 4) :=
    rawProdSet 2 2
      (reindexSet swapFin2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}))
      (Set.univ : Set (Rn 2))
  let LtVals : Set (Rn 4) :=
    rawProdSet 2 2 (Set.univ : Set (Rn 2))
      (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  GG ∩ GtXY ∩ LtValsᶜ

/-- The raw reverse-order non-rise witness set is definable. -/
theorem definable_nonRiseToWitnessSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (nonRiseToWitnessSet f a b) := by
  let G : Set (Rn 2) := encodeSet (ℝ × ℝ) (rawGraph (Set.Ioo a b) f)
  let GG : Set (Rn 4) := reindexSet swapFin4Mid (rawProdSet 2 2 G G)
  let GtXY : Set (Rn 4) :=
    rawProdSet 2 2
      (reindexSet swapFin2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}))
      (Set.univ : Set (Rn 2))
  let LtVals : Set (Rn 4) :=
    rawProdSet 2 2 (Set.univ : Set (Rn 2))
      (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  have hG : S.Definable G := by
    simpa [G, DefinableMapOf, DefinableSetOf] using hf
  have hLt : S.Definable (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) := by
    simpa [DefinableSetOf] using S.definableLt
  have hGt : S.Definable (reindexSet swapFin2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})) := by
    exact S.definableReindex swapFin2 hLt
  have hGG : S.Definable GG := by
    dsimp [GG]
    exact S.definableReindex swapFin4Mid (S.definable_prod hG hG)
  have hGtXY : S.Definable GtXY := by
    dsimp [GtXY]
    exact S.definable_prod hGt S.definable_univ
  have hLtVals : S.Definable LtVals := by
    dsimp [LtVals]
    exact S.definable_prod S.definable_univ hLt
  dsimp [nonRiseToWitnessSet, G, GG, GtXY, LtVals]
  exact S.definable_inter (S.definable_inter hGG hGtXY) (S.definable_compl hLtVals)

@[simp] theorem fin_append_append_mem_nonRiseToWitnessSet
    {f : ℝ → ℝ} {a b : ℝ} {x y fx fy : Rn 1} :
    Fin.append (Fin.append x y) (Fin.append fx fy) ∈ nonRiseToWitnessSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar y ∈ Set.Ioo a b ∧
      rn1ToScalar fx = f (rn1ToScalar x) ∧
      rn1ToScalar fy = f (rn1ToScalar y) ∧
      rn1ToScalar y < rn1ToScalar x ∧
      ¬ rn1ToScalar fx < rn1ToScalar fy := by
  dsimp [nonRiseToWitnessSet]
  rw [mem_inter_iff, mem_inter_iff]
  rw [mem_reindexSet, reindexRn_swapFin4Mid_quad]
  rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real_prod, splitAtEquiv_fin_append,
    mem_encodeSet_real_prod, splitAtEquiv_fin_append]
  rw [mem_rawProdSet, splitAtEquiv_fin_append, mem_reindexSet, reindexRn_swapFin2_fin_append,
    mem_encodeSet_real_prod]
  rw [mem_compl_iff, mem_rawProdSet, splitAtEquiv_fin_append, mem_encodeSet_real_prod]
  have hsecondVals :
      ((splitAtEquiv 2 2) (Fin.append (Fin.append x y) (Fin.append fx fy))).2 = Fin.append fx fy := by
    simpa using congrArg Prod.snd
      (splitAtEquiv_fin_append (m := 2) (n := 2) (x := Fin.append x y) (y := Fin.append fx fy))
  have hsplitVals :
      (splitAtEquiv 1 1) ((splitAtEquiv 2 2) (Fin.append (Fin.append x y) (Fin.append fx fy))).2 =
        (fx, fy) := by
    simpa [hsecondVals] using (splitAtEquiv_fin_append (m := 1) (n := 1) (x := fx) (y := fy))
  simp [hsplitVals, rawGraph, and_assoc, and_left_comm, and_comm]

/-- Raw pairs `(x, y)` with `y < x` and `f y ≤ f x`. -/
def nonRiseToPairSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  prefixProjection 2 2 (nonRiseToWitnessSet f a b)

/-- The raw reverse-order non-rise pair set is definable. -/
theorem definable_nonRiseToPairSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (nonRiseToPairSet f a b) :=
  S.definable_projection (definable_nonRiseToWitnessSet (S := S) (f := f) (a := a) (b := b) hf)

@[simp] theorem fin_append_mem_nonRiseToPairSet
    {f : ℝ → ℝ} {a b : ℝ} {x y : Rn 1} :
    Fin.append x y ∈ nonRiseToPairSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar y ∈ Set.Ioo a b ∧
      rn1ToScalar y < rn1ToScalar x ∧
      ¬ f (rn1ToScalar x) < f (rn1ToScalar y) := by
  constructor
  · intro hxy
    rcases hxy with ⟨z, hz⟩
    let fx : Rn 1 := (splitAtEquiv 1 1 z).1
    let fy : Rn 1 := (splitAtEquiv 1 1 z).2
    have hzEq : z = Fin.append fx fy := by
      have hz0 : z = (splitAtEquiv 1 1).symm (((splitAtEquiv 1 1) z).1, ((splitAtEquiv 1 1) z).2) := by
        simpa using (Equiv.symm_apply_apply (splitAtEquiv 1 1) z).symm
      have hz1 :
          (splitAtEquiv 1 1).symm (((splitAtEquiv 1 1) z).1, ((splitAtEquiv 1 1) z).2) =
            Fin.append fx fy := by
        simpa [fx, fy] using
          (splitAtEquiv_symm_apply (((splitAtEquiv 1 1) z).1) (((splitAtEquiv 1 1) z).2))
      exact hz0.trans hz1
    rw [hzEq] at hz
    rcases (fin_append_append_mem_nonRiseToWitnessSet (x := x) (y := y) (fx := fx) (fy := fy)).mp hz
      with ⟨hxIoo, hyIoo, hfx, hfy, hyxlt, hnotlt⟩
    simpa [fx, fy] using ⟨hxIoo, hyIoo, hyxlt, by simpa [hfx, hfy] using hnotlt⟩
  · rintro ⟨hxIoo, hyIoo, hyxlt, hnotlt⟩
    refine ⟨Fin.append (scalarToRn1 (f (rn1ToScalar x))) (scalarToRn1 (f (rn1ToScalar y))), ?_⟩
    simpa [rn1ToScalar_scalarToRn1] using
      (fin_append_append_mem_nonRiseToWitnessSet
        (x := x) (y := y)
        (fx := scalarToRn1 (f (rn1ToScalar x)))
        (fy := scalarToRn1 (f (rn1ToScalar y)))).2
        ⟨hxIoo, hyIoo, rfl, rfl, hyxlt, by simpa [rn1ToScalar_scalarToRn1] using hnotlt⟩

/-- Raw triples `(x, y, z)` where `(x,z)` is a non-rise pair and `z ≤ y`. -/
def badRightAboveTripleSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 3) :=
  let P : Set (Rn 2) := nonRisePairSet f a b
  let Pxz : Set (Rn 3) := reindexSet swapFin3Tail (rawProdSet 2 1 P (Set.univ : Set (Rn 1)))
  let LtYZ : Set (Rn 3) :=
    rawProdSet 1 2 (Set.univ : Set (Rn 1))
      (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  Pxz ∩ LtYZᶜ

/-- The bad-right-above triple set is definable. -/
theorem definable_badRightAboveTripleSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (badRightAboveTripleSet f a b) := by
  let P : Set (Rn 2) := nonRisePairSet f a b
  let Pxz : Set (Rn 3) := reindexSet swapFin3Tail (rawProdSet 2 1 P (Set.univ : Set (Rn 1)))
  let LtYZ : Set (Rn 3) :=
    rawProdSet 1 2 (Set.univ : Set (Rn 1))
      (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  have hP : S.Definable P := definable_nonRisePairSet (S := S) (f := f) (a := a) (b := b) hf
  have hPxz : S.Definable Pxz := by
    dsimp [Pxz]
    exact S.definableReindex swapFin3Tail (S.definable_prod hP S.definable_univ)
  have hLt : S.Definable (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) := by
    simpa [DefinableSetOf] using S.definableLt
  have hLtYZ : S.Definable LtYZ := by
    dsimp [LtYZ]
    exact S.definable_prod S.definable_univ hLt
  dsimp [badRightAboveTripleSet, P, Pxz, LtYZ]
  exact S.definable_inter hPxz (S.definable_compl hLtYZ)

@[simp] theorem fin_append_triple_mem_badRightAboveTripleSet
    {f : ℝ → ℝ} {a b : ℝ} {x y z : Rn 1} :
    Fin.append (Fin.append x y) z ∈ badRightAboveTripleSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar z ∈ Set.Ioo a b ∧
      rn1ToScalar x < rn1ToScalar z ∧
      ¬ f (rn1ToScalar x) < f (rn1ToScalar z) ∧
      rn1ToScalar z ≤ rn1ToScalar y := by
  dsimp [badRightAboveTripleSet]
  rw [mem_inter_iff]
  rw [mem_reindexSet, reindexRn_swapFin3Tail_triple, mem_rawProdSet, splitAtEquiv_fin_append,
    fin_append_mem_nonRisePairSet]
  rw [mem_compl_iff, fin_append_assoc_rn1, mem_rawProdSet, splitAtEquiv_fin_append,
    fin_append_mem_ltPairSet]
  simp [and_assoc, and_left_comm, and_comm, not_lt]

/-- Raw pairs `(x,y)` such that there is a non-rise witness `z` with `x < z ≤ y`. -/
def badRightAbovePairSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  prefixProjection 2 1 (badRightAboveTripleSet f a b)

/-- The bad-right-above pair set is definable. -/
theorem definable_badRightAbovePairSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (badRightAbovePairSet f a b) :=
  S.definable_projection (definable_badRightAboveTripleSet (S := S) (f := f) (a := a) (b := b) hf)

@[simp] theorem fin_append_mem_badRightAbovePairSet
    {f : ℝ → ℝ} {a b : ℝ} {x y : Rn 1} :
    Fin.append x y ∈ badRightAbovePairSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      ∃ z : ℝ,
        z ∈ Set.Ioo a b ∧
        rn1ToScalar x < z ∧
        ¬ f (rn1ToScalar x) < f z ∧
        z ≤ rn1ToScalar y := by
  constructor
  · intro hxy
    rcases hxy with ⟨z, hz⟩
    rcases (fin_append_triple_mem_badRightAboveTripleSet (x := x) (y := y) (z := z)).mp hz with
      ⟨hxIoo, hzIoo, hxz, hnotlt, hzy⟩
    exact ⟨hxIoo, rn1ToScalar z, hzIoo, hxz, by simpa using hnotlt, hzy⟩
  · rintro ⟨hxIoo, z, hzIoo, hxz, hnotlt, hzy⟩
    refine ⟨scalarToRn1 z, ?_⟩
    simpa [rn1ToScalar_scalarToRn1] using
      (fin_append_triple_mem_badRightAboveTripleSet (x := x) (y := y) (z := scalarToRn1 z)).2
        ⟨hxIoo, by simpa using hzIoo, hxz,
          by simpa [rn1ToScalar_scalarToRn1] using hnotlt, hzy⟩

/-- Uniform pair-level version of `rightAboveSet`. -/
def rightAbovePairSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (Set.Ioo a b)) ∩
    encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2} ∩
      (badRightAbovePairSet f a b)ᶜ

/-- The uniform right-above pair set is definable. -/
theorem definable_rightAbovePairSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (rightAbovePairSet f a b) := by
  have hIoo : S.Definable (encodeSet ℝ (Set.Ioo a b)) := by
    simpa [DefinableSetOf] using S.definableIoo a b
  have hProd : S.Definable (rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (Set.Ioo a b))) := by
    exact S.definable_prod hIoo hIoo
  have hLt : S.Definable (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) := by
    simpa [DefinableSetOf] using S.definableLt
  have hBad : S.Definable (badRightAbovePairSet f a b) :=
    definable_badRightAbovePairSet (S := S) (f := f) (a := a) (b := b) hf
  dsimp [rightAbovePairSet]
  exact S.definable_inter (S.definable_inter hProd hLt) (S.definable_compl hBad)

@[simp] theorem fin_append_mem_rightAbovePairSet
    {f : ℝ → ℝ} {a b : ℝ} {x y : Rn 1} :
    Fin.append x y ∈ rightAbovePairSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar y ∈ Set.Ioo a b ∧
      rn1ToScalar x < rn1ToScalar y ∧
      ∀ z ∈ Set.Ioc (rn1ToScalar x) (rn1ToScalar y), f z > f (rn1ToScalar x) := by
  rw [rightAbovePairSet, mem_inter_iff, mem_inter_iff, mem_rawProdSet, splitAtEquiv_fin_append,
    mem_encodeSet_real, mem_encodeSet_real, fin_append_mem_ltPairSet, mem_compl_iff,
    fin_append_mem_badRightAbovePairSet]
  constructor
  · rintro ⟨⟨⟨hxIoo, hyIoo⟩, hxy⟩, hbad⟩
    refine ⟨hxIoo, hyIoo, hxy, ?_⟩
    intro z hz
    by_contra hnotgt
    apply hbad
    refine ⟨hxIoo, z, ?_, hz.1, ?_, hz.2⟩
    · exact ⟨lt_trans hxIoo.1 hz.1, lt_of_le_of_lt hz.2 hyIoo.2⟩
    · simpa using hnotgt
  · rintro ⟨hxIoo, hyIoo, hxy, habove⟩
    refine ⟨⟨⟨hxIoo, hyIoo⟩, hxy⟩, ?_⟩
    intro hbad
    rcases hbad with ⟨-, z, hzIoo, hxz, hnotlt, hzy⟩
    exact hnotlt (habove z ⟨hxz, hzy⟩)

/-- Raw triples `(x, y, z)` where `(x,z)` is a reverse-order non-rise pair and `y ≤ z`. -/
def badLeftAboveTripleSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 3) :=
  let P : Set (Rn 2) := nonRiseToPairSet f a b
  let Pxz : Set (Rn 3) := reindexSet swapFin3Tail (rawProdSet 2 1 P (Set.univ : Set (Rn 1)))
  let LtZY : Set (Rn 3) :=
    reindexSet swapFin3Tail <|
      rawProdSet 1 2 (Set.univ : Set (Rn 1))
        (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  Pxz ∩ LtZYᶜ

/-- The bad-left-above triple set is definable. -/
theorem definable_badLeftAboveTripleSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (badLeftAboveTripleSet f a b) := by
  let P : Set (Rn 2) := nonRiseToPairSet f a b
  let Pxz : Set (Rn 3) := reindexSet swapFin3Tail (rawProdSet 2 1 P (Set.univ : Set (Rn 1)))
  let LtZY : Set (Rn 3) :=
    reindexSet swapFin3Tail <|
      rawProdSet 1 2 (Set.univ : Set (Rn 1))
        (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})
  have hP : S.Definable P := definable_nonRiseToPairSet (S := S) (f := f) (a := a) (b := b) hf
  have hPxz : S.Definable Pxz := by
    dsimp [Pxz]
    exact S.definableReindex swapFin3Tail (S.definable_prod hP S.definable_univ)
  have hLt : S.Definable (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) := by
    simpa [DefinableSetOf] using S.definableLt
  have hLtZY : S.Definable LtZY := by
    dsimp [LtZY]
    exact S.definableReindex swapFin3Tail (S.definable_prod S.definable_univ hLt)
  dsimp [badLeftAboveTripleSet, P, Pxz, LtZY]
  exact S.definable_inter hPxz (S.definable_compl hLtZY)

@[simp] theorem fin_append_triple_mem_badLeftAboveTripleSet
    {f : ℝ → ℝ} {a b : ℝ} {x y z : Rn 1} :
    Fin.append (Fin.append x y) z ∈ badLeftAboveTripleSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar z ∈ Set.Ioo a b ∧
      rn1ToScalar z < rn1ToScalar x ∧
      ¬ f (rn1ToScalar x) < f (rn1ToScalar z) ∧
      rn1ToScalar y ≤ rn1ToScalar z := by
  dsimp [badLeftAboveTripleSet]
  rw [mem_inter_iff]
  rw [mem_reindexSet, reindexRn_swapFin3Tail_triple, mem_rawProdSet, splitAtEquiv_fin_append,
    fin_append_mem_nonRiseToPairSet]
  rw [mem_compl_iff, mem_reindexSet, reindexRn_swapFin3Tail_triple, fin_append_assoc_rn1,
    mem_rawProdSet, splitAtEquiv_fin_append, fin_append_mem_ltPairSet]
  simp [and_assoc, and_left_comm, and_comm, not_lt]

/-- Raw pairs `(x,y)` such that there is a non-rise witness `z` with `y ≤ z < x`. -/
def badLeftAbovePairSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  prefixProjection 2 1 (badLeftAboveTripleSet f a b)

/-- The bad-left-above pair set is definable. -/
theorem definable_badLeftAbovePairSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (badLeftAbovePairSet f a b) :=
  S.definable_projection (definable_badLeftAboveTripleSet (S := S) (f := f) (a := a) (b := b) hf)

@[simp] theorem fin_append_mem_badLeftAbovePairSet
    {f : ℝ → ℝ} {a b : ℝ} {x y : Rn 1} :
    Fin.append x y ∈ badLeftAbovePairSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      ∃ z : ℝ,
        z ∈ Set.Ioo a b ∧
        z < rn1ToScalar x ∧
        ¬ f (rn1ToScalar x) < f z ∧
        rn1ToScalar y ≤ z := by
  constructor
  · intro hxy
    rcases hxy with ⟨z, hz⟩
    rcases (fin_append_triple_mem_badLeftAboveTripleSet (x := x) (y := y) (z := z)).mp hz with
      ⟨hxIoo, hzIoo, hzx, hnotlt, hyz⟩
    exact ⟨hxIoo, rn1ToScalar z, hzIoo, hzx, by simpa using hnotlt, hyz⟩
  · rintro ⟨hxIoo, z, hzIoo, hzx, hnotlt, hyz⟩
    refine ⟨scalarToRn1 z, ?_⟩
    simpa [rn1ToScalar_scalarToRn1] using
      (fin_append_triple_mem_badLeftAboveTripleSet (x := x) (y := y) (z := scalarToRn1 z)).2
        ⟨hxIoo, by simpa using hzIoo, hzx,
          by simpa [rn1ToScalar_scalarToRn1] using hnotlt, hyz⟩

/-- Uniform pair-level version of `leftAboveSet`. -/
def leftAbovePairSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 2) :=
  rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (Set.Ioo a b)) ∩
    reindexSet swapFin2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) ∩
      (badLeftAbovePairSet f a b)ᶜ

/-- The uniform left-above pair set is definable. -/
theorem definable_leftAbovePairSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (leftAbovePairSet f a b) := by
  have hIoo : S.Definable (encodeSet ℝ (Set.Ioo a b)) := by
    simpa [DefinableSetOf] using S.definableIoo a b
  have hProd : S.Definable
      (rawProdSet 1 1 (encodeSet ℝ (Set.Ioo a b)) (encodeSet ℝ (Set.Ioo a b))) := by
    exact S.definable_prod hIoo hIoo
  have hLt : S.Definable (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2}) := by
    simpa [DefinableSetOf] using S.definableLt
  have hGt : S.Definable
      (reindexSet swapFin2 (encodeSet (ℝ × ℝ) {p : ℝ × ℝ | p.1 < p.2})) := by
    exact S.definableReindex swapFin2 hLt
  have hBad : S.Definable (badLeftAbovePairSet f a b) :=
    definable_badLeftAbovePairSet (S := S) (f := f) (a := a) (b := b) hf
  dsimp [leftAbovePairSet]
  exact S.definable_inter (S.definable_inter hProd hGt) (S.definable_compl hBad)

@[simp] theorem fin_append_mem_leftAbovePairSet
    {f : ℝ → ℝ} {a b : ℝ} {x y : Rn 1} :
    Fin.append x y ∈ leftAbovePairSet f a b ↔
      rn1ToScalar x ∈ Set.Ioo a b ∧
      rn1ToScalar y ∈ Set.Ioo a b ∧
      rn1ToScalar y < rn1ToScalar x ∧
      ∀ z ∈ Set.Ico (rn1ToScalar y) (rn1ToScalar x), f z > f (rn1ToScalar x) := by
  rw [leftAbovePairSet, mem_inter_iff, mem_inter_iff, mem_rawProdSet, splitAtEquiv_fin_append,
    mem_encodeSet_real, mem_encodeSet_real, mem_reindexSet, reindexRn_swapFin2_fin_append,
    fin_append_mem_ltPairSet, mem_compl_iff, fin_append_mem_badLeftAbovePairSet]
  constructor
  · rintro ⟨⟨⟨hxIoo, hyIoo⟩, hyx⟩, hbad⟩
    refine ⟨hxIoo, hyIoo, hyx, ?_⟩
    intro z hz
    by_contra hnotgt
    apply hbad
    refine ⟨hxIoo, z, ?_, hz.2, ?_, hz.1⟩
    · exact ⟨lt_of_lt_of_le hyIoo.1 hz.1, lt_trans hz.2 hxIoo.2⟩
    · simpa using hnotgt
  · rintro ⟨hxIoo, hyIoo, hyx, habove⟩
    refine ⟨⟨⟨hxIoo, hyIoo⟩, hyx⟩, ?_⟩
    intro hbad
    rcases hbad with ⟨-, z, hzIoo, hzx, hnotlt, hyz⟩
    exact hnotlt (habove z ⟨hyz, hzx⟩)

/-- Base points admitting a left `plus`-witness interval. -/
def leftAbovePointSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 1) :=
  prefixProjection 1 1 (leftAbovePairSet f a b)

/-- Base points admitting a right `plus`-witness interval. -/
def rightAbovePointSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 1) :=
  prefixProjection 1 1 (rightAbovePairSet f a b)

/-- The left `plus`-witness point set is definable. -/
theorem definable_leftAbovePointSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (leftAbovePointSet f a b) :=
  S.definable_projection (definable_leftAbovePairSet (S := S) (f := f) (a := a) (b := b) hf)

/-- The right `plus`-witness point set is definable. -/
theorem definable_rightAbovePointSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (rightAbovePointSet f a b) :=
  S.definable_projection (definable_rightAbovePairSet (S := S) (f := f) (a := a) (b := b) hf)

@[simp] theorem scalarToRn1_mem_leftAbovePointSet
    {f : ℝ → ℝ} {a b x : ℝ} :
    scalarToRn1 x ∈ leftAbovePointSet f a b ↔
      x ∈ Set.Ioo a b ∧ (leftSignSet .plus f a b x).Nonempty := by
  rw [leftAbovePointSet, mem_prefixProjection]
  constructor
  · rintro ⟨y, hy⟩
    rcases (fin_append_mem_leftAbovePairSet (x := scalarToRn1 x) (y := y)).mp hy with
      ⟨hxIoo, hyIoo, hyx, habove⟩
    refine ⟨hxIoo, ⟨rn1ToScalar y, ?_⟩⟩
    exact ⟨hyIoo, hyx, by simpa [localSignRel_plus] using habove⟩
  · rintro ⟨hxIoo, ⟨y, hyIoo, hyx, habove⟩⟩
    refine ⟨scalarToRn1 y, ?_⟩
    simpa [rn1ToScalar_scalarToRn1] using
      (fin_append_mem_leftAbovePairSet (x := scalarToRn1 x) (y := scalarToRn1 y)).2
        ⟨by simpa [rn1ToScalar_scalarToRn1] using hxIoo,
          by simpa [rn1ToScalar_scalarToRn1] using hyIoo,
          by simpa [rn1ToScalar_scalarToRn1] using hyx,
          by simpa [localSignRel_plus, rn1ToScalar_scalarToRn1] using habove⟩

@[simp] theorem scalarToRn1_mem_rightAbovePointSet
    {f : ℝ → ℝ} {a b x : ℝ} :
    scalarToRn1 x ∈ rightAbovePointSet f a b ↔
      x ∈ Set.Ioo a b ∧ (rightSignSet .plus f a b x).Nonempty := by
  rw [rightAbovePointSet, mem_prefixProjection]
  constructor
  · rintro ⟨y, hy⟩
    rcases (fin_append_mem_rightAbovePairSet (x := scalarToRn1 x) (y := y)).mp hy with
      ⟨hxIoo, hyIoo, hxy, habove⟩
    refine ⟨hxIoo, ⟨rn1ToScalar y, ?_⟩⟩
    exact ⟨hyIoo, hxy, by simpa [localSignRel_plus] using habove⟩
  · rintro ⟨hxIoo, ⟨y, hyIoo, hxy, habove⟩⟩
    refine ⟨scalarToRn1 y, ?_⟩
    simpa [rn1ToScalar_scalarToRn1] using
      (fin_append_mem_rightAbovePairSet (x := scalarToRn1 x) (y := scalarToRn1 y)).2
        ⟨by simpa [rn1ToScalar_scalarToRn1] using hxIoo,
          by simpa [rn1ToScalar_scalarToRn1] using hyIoo,
          by simpa [rn1ToScalar_scalarToRn1] using hxy,
          by simpa [localSignRel_plus, rn1ToScalar_scalarToRn1] using habove⟩

/-- The definable raw point set of Coste's `Φ+,+` pattern. -/
def locPatternPPPointSet (f : ℝ → ℝ) (a b : ℝ) : Set (Rn 1) :=
  leftAbovePointSet f a b ∩ rightAbovePointSet f a b

/-- The `Φ+,+` point set is definable. -/
theorem definable_locPatternPPPointSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    S.Definable (locPatternPPPointSet f a b) := by
  exact S.definable_inter
    (definable_leftAbovePointSet (S := S) (f := f) (a := a) (b := b) hf)
    (definable_rightAbovePointSet (S := S) (f := f) (a := a) (b := b) hf)

@[simp] theorem scalarToRn1_mem_locPatternPPPointSet
    {f : ℝ → ℝ} {a b x : ℝ} :
    scalarToRn1 x ∈ locPatternPPPointSet f a b ↔ locPattern_pp f a b x := by
  rw [locPatternPPPointSet, mem_inter_iff, scalarToRn1_mem_leftAbovePointSet,
    scalarToRn1_mem_rightAbovePointSet]
  constructor
  · rintro ⟨⟨-, hleft⟩, ⟨-, hright⟩⟩
    exact (locPattern_iff_nonempty_leftSignSet_rightSignSet
      (f := f) (a := a) (b := b) (x := x) (l := .plus) (r := .plus)).2 ⟨hleft, hright⟩
  · intro hpat
    have hxIoo : x ∈ Set.Ioo a b := mem_Ioo_of_locPattern hpat
    rcases (locPattern_iff_nonempty_leftSignSet_rightSignSet
      (f := f) (a := a) (b := b) (x := x) (l := .plus) (r := .plus)).mp hpat with
      ⟨hleft, hright⟩
    exact ⟨⟨hxIoo, hleft⟩, ⟨hxIoo, hright⟩⟩

/-- The set of real points satisfying Coste's `Φ+,+` pattern is definable. -/
theorem definable_locPatternPPSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable {x : ℝ | locPattern_pp f a b x} := by
  have hRaw : S.Definable (locPatternPPPointSet f a b) :=
    definable_locPatternPPPointSet (S := S) (f := f) (a := a) (b := b) hf
  have hEq : locPatternPPPointSet f a b = encodeSet ℝ {x : ℝ | locPattern_pp f a b x} := by
    ext x
    simpa [mem_encodeSet_real, scalarToRn1_rn1ToScalar] using
      (scalarToRn1_mem_locPatternPPPointSet (f := f) (a := a) (b := b) (x := rn1ToScalar x))
  simpa [DefinableSetOf, hEq] using hRaw

/-- An infinite family of `Φ+,+` points contains a nontrivial open interval. -/
theorem exists_Ioo_subset_locPatternPP_of_infinite {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hInf : {x : ℝ | locPattern_pp f a b x}.Infinite) :
    ∃ u v : ℝ, u < v ∧ ∀ x ∈ Set.Ioo u v, locPattern_pp f a b x := by
  have hDef : DefinableSetOf S.Definable {x : ℝ | locPattern_pp f a b x} :=
    definable_locPatternPPSet (S := S) (f := f) (a := a) (b := b) hf
  rcases definable_infinite_subset_real_contains_Ioo (S := S) hDef hInf with
    ⟨u, v, huv, hsub⟩
  exact ⟨u, v, huv, fun x hx => hsub hx⟩

/-- Negating turns Coste's `Φ+,+` pattern into `Φ−,−`. -/
theorem locPattern_pp_neg_iff_locPattern_mm {f : ℝ → ℝ} {a b x : ℝ} :
    locPattern_pp (fun t => -f t) a b x ↔ locPattern_mm f a b x := by
  constructor
  · rintro ⟨ε, hεpos, hsub, hleft, hright⟩
    refine ⟨ε, hεpos, hsub, ?_, ?_⟩
    · intro y hy1 hy2
      exact neg_lt_neg_iff.mp (hleft y hy1 hy2)
    · intro y hy1 hy2
      exact neg_lt_neg_iff.mp (hright y hy1 hy2)
  · rintro ⟨ε, hεpos, hsub, hleft, hright⟩
    refine ⟨ε, hεpos, hsub, ?_, ?_⟩
    · intro y hy1 hy2
      exact neg_lt_neg (hleft y hy1 hy2)
    · intro y hy1 hy2
      exact neg_lt_neg (hright y hy1 hy2)

/-- Coste's set `B` is definable: it is the interval minus the projection of the non-rise pairs. -/
theorem definable_eventuallyAboveSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (eventuallyAboveSet f a b) := by
  let W : Set ℝ :=
    {x : ℝ | x ∈ Set.Ioo a b ∧ ∃ y ∈ Set.Ioo a b, x < y ∧ ¬ f x < f y}
  let P : Set (Rn 2) := nonRisePairSet f a b
  have hP : S.Definable P := definable_nonRisePairSet (S := S) (f := f) (a := a) (b := b) hf
  have hProj : S.Definable (prefixProjection 1 1 P) := S.definable_projection hP
  have hProjEq : prefixProjection 1 1 P = encodeSet ℝ W := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy⟩
      rcases (fin_append_mem_nonRisePairSet (x := x) (y := y)).mp hy with
        ⟨hxIoo, hyIoo, hxy, hnotlt⟩
      have hxW : rn1ToScalar x ∈ W := by
        refine ⟨hxIoo, rn1ToScalar y, hyIoo, hxy, hnotlt⟩
      simpa [W, mem_encodeSet_real] using hxW
    · intro hx
      have hxW : rn1ToScalar x ∈ W := by
        simpa [W, mem_encodeSet_real] using hx
      rcases hxW with ⟨hxIoo, y, hyIoo, hxy, hnotlt⟩
      refine ⟨scalarToRn1 y, ?_⟩
      simpa [P, rn1ToScalar_scalarToRn1] using
        (fin_append_mem_nonRisePairSet
          (x := x) (y := scalarToRn1 y)).2
          ⟨hxIoo, by simpa using hyIoo, hxy, by simpa [rn1ToScalar_scalarToRn1] using hnotlt⟩
  have hEventEq : eventuallyAboveSet f a b = Set.Ioo a b ∩ Wᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxW
      rcases hxW with ⟨-, y, hyIoo, hxy, hnotlt⟩
      exact hnotlt (hx.2 y hyIoo hxy)
    · rintro ⟨hxIoo, hxW⟩
      refine ⟨hxIoo, ?_⟩
      intro y hyIoo hxy
      by_contra hnotgt
      exact hxW ⟨hxIoo, y, hyIoo, hxy, by simpa using hnotgt⟩
  have hWDef : S.Definable (encodeSet ℝ W) := by
    simpa [hProjEq] using hProj
  have hIoo : S.Definable (encodeSet ℝ (Set.Ioo a b)) := by
    simpa [DefinableSetOf] using S.definableIoo a b
  simpa [DefinableSetOf, hEventEq] using S.definable_inter hIoo (S.definable_compl hWDef)

/-- The leftward analogue of Coste's set `B` is definable: it is the interval minus the
projection of the reverse-order non-rise pairs. -/
theorem definable_eventuallyBelowSet {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) :
    DefinableSetOf S.Definable (eventuallyBelowSet f a b) := by
  let W : Set ℝ :=
    {x : ℝ | x ∈ Set.Ioo a b ∧ ∃ y ∈ Set.Ioo a b, y < x ∧ ¬ f x < f y}
  let P : Set (Rn 2) := nonRiseToPairSet f a b
  have hP : S.Definable P :=
    definable_nonRiseToPairSet (S := S) (f := f) (a := a) (b := b) hf
  have hProj : S.Definable (prefixProjection 1 1 P) := S.definable_projection hP
  have hProjEq : prefixProjection 1 1 P = encodeSet ℝ W := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy⟩
      rcases (fin_append_mem_nonRiseToPairSet (x := x) (y := y)).mp hy with
        ⟨hxIoo, hyIoo, hyx, hnotlt⟩
      have hxW : rn1ToScalar x ∈ W := by
        exact ⟨hxIoo, rn1ToScalar y, hyIoo, hyx, hnotlt⟩
      simpa [W, mem_encodeSet_real] using hxW
    · intro hx
      have hxW : rn1ToScalar x ∈ W := by
        simpa [W, mem_encodeSet_real] using hx
      rcases hxW with ⟨hxIoo, y, hyIoo, hyx, hnotlt⟩
      refine ⟨scalarToRn1 y, ?_⟩
      simpa [P, rn1ToScalar_scalarToRn1] using
        (fin_append_mem_nonRiseToPairSet (x := x) (y := scalarToRn1 y)).2
          ⟨hxIoo, by simpa using hyIoo, hyx, by simpa [rn1ToScalar_scalarToRn1] using hnotlt⟩
  have hEventEq : eventuallyBelowSet f a b = Set.Ioo a b ∩ Wᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxW
      rcases hxW with ⟨-, y, hyIoo, hyx, hnotlt⟩
      exact hnotlt (hx.2 y hyIoo hyx)
    · rintro ⟨hxIoo, hxW⟩
      refine ⟨hxIoo, ?_⟩
      intro y hyIoo hyx
      by_contra hnotgt
      exact hxW ⟨hxIoo, y, hyIoo, hyx, by simpa using hnotgt⟩
  have hWDef : S.Definable (encodeSet ℝ W) := by
    simpa [hProjEq] using hProj
  have hIoo : S.Definable (encodeSet ℝ (Set.Ioo a b)) := by
    simpa [DefinableSetOf] using S.definableIoo a b
  simpa [DefinableSetOf, hEventEq] using S.definable_inter hIoo (S.definable_compl hWDef)

/-- If every point of an interval lies in Coste's set `B`, then the function is strictly increasing
on that interval. -/
theorem strictMonoOn_of_subset_eventuallyAboveSet {f : ℝ → ℝ} {a b u v : ℝ}
    (hsub : Set.Ioo u v ⊆ eventuallyAboveSet f a b) :
    StrictMonoOn f (Set.Ioo u v) := by
  intro x hx y hy hxy
  exact (hsub hx).2 y (hsub hy).1 hxy

/-- If every point of an interval lies in the leftward analogue of Coste's set `B`, then the
function is strictly decreasing on that interval. -/
theorem strictAntiOn_of_subset_eventuallyBelowSet {f : ℝ → ℝ} {a b u v : ℝ}
    (hsub : Set.Ioo u v ⊆ eventuallyBelowSet f a b) :
    StrictAntiOn f (Set.Ioo u v) := by
  intro x hx y hy hxy
  exact (hsub hy).2 x (hsub hx).1 hxy

/-- A strictly increasing function cannot satisfy `Φ+,+` at a point. -/
theorem not_locPattern_pp_at_of_strictMonoOn {f : ℝ → ℝ} {a b x : ℝ}
    (hmono : StrictMonoOn f (Set.Ioo a b)) (hx : x ∈ Set.Ioo a b) :
    ¬ locPattern_pp f a b x := by
  intro hpp
  rcases hpp with ⟨ε, hεpos, hεsub, hleft, -⟩
  let y : ℝ := x - ε / 2
  have hy_left : x - ε < y := by
    dsimp [y]
    linarith
  have hy_right : y < x := by
    dsimp [y]
    linarith
  have hy : y ∈ Set.Ioo a b := hεsub ⟨hy_left, by
    dsimp [y]
    linarith⟩
  have hfy_gt : f y > f x := hleft y hy_left hy_right
  have hfy_lt : f y < f x := hmono hy hx hy_right
  exact (not_lt_of_gt hfy_lt) hfy_gt

/-- A strictly increasing function cannot satisfy `Φ+,+` at every point of a nontrivial
interval. -/
theorem not_locPattern_pp_on_Ioo_of_strictMonoOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hmono : StrictMonoOn f (Set.Ioo a b))
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pp f a b x) :
    False := by
  obtain ⟨x, hx⟩ := exists_between hab
  exact not_locPattern_pp_at_of_strictMonoOn hmono hx (hpat x hx)

/-- A strictly decreasing function cannot satisfy `Φ+,+` at a point. -/
theorem not_locPattern_pp_at_of_strictAntiOn {f : ℝ → ℝ} {a b x : ℝ}
    (hanti : StrictAntiOn f (Set.Ioo a b)) (hx : x ∈ Set.Ioo a b) :
    ¬ locPattern_pp f a b x := by
  intro hpp
  rcases hpp with ⟨ε, hεpos, hεsub, -, hright⟩
  let y : ℝ := x + ε / 2
  have hy_left : x < y := by
    dsimp [y]
    linarith
  have hy_right : y < x + ε := by
    dsimp [y]
    linarith
  have hy : y ∈ Set.Ioo a b := hεsub ⟨by
    dsimp [y]
    linarith, hy_right⟩
  have hfy_gt : f y > f x := hright y hy_left hy_right
  have hfy_lt : f y < f x := hanti hx hy hy_left
  exact (not_lt_of_gt hfy_gt) hfy_lt

/-- A strictly decreasing function cannot satisfy `Φ+,+` at every point of a nontrivial
interval. -/
theorem not_locPattern_pp_on_Ioo_of_strictAntiOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hanti : StrictAntiOn f (Set.Ioo a b))
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pp f a b x) :
    False := by
  obtain ⟨x, hx⟩ := exists_between hab
  exact not_locPattern_pp_at_of_strictAntiOn hanti hx (hpat x hx)

/-- A strictly decreasing function cannot satisfy `Φ−,−` at a point. -/
theorem not_locPattern_mm_at_of_strictAntiOn {f : ℝ → ℝ} {a b x : ℝ}
    (hanti : StrictAntiOn f (Set.Ioo a b)) (hx : x ∈ Set.Ioo a b) :
    ¬ locPattern_mm f a b x := by
  intro hmm
  have hmono : StrictMonoOn (fun t => -f t) (Set.Ioo a b) := by
    intro y hy z hz hyz
    exact neg_lt_neg (hanti hy hz hyz)
  have hppNeg : locPattern_pp (fun t => -f t) a b x :=
    (locPattern_pp_neg_iff_locPattern_mm (f := f) (a := a) (b := b) (x := x)).2 hmm
  exact not_locPattern_pp_at_of_strictMonoOn hmono hx hppNeg

/-- A strictly decreasing function cannot satisfy `Φ−,−` at every point of a nontrivial
interval. -/
theorem not_locPattern_mm_on_Ioo_of_strictAntiOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hanti : StrictAntiOn f (Set.Ioo a b))
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_mm f a b x) :
    False := by
  obtain ⟨x, hx⟩ := exists_between hab
  exact not_locPattern_mm_at_of_strictAntiOn hanti hx (hpat x hx)

/-- If every point of an interval satisfies `Φ+,+`, then Coste's set `B` is finite there. -/
theorem finite_eventuallyAboveSet_of_locPattern_pp_on_Ioo
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pp f a b x) :
    (eventuallyAboveSet f a b).Finite := by
  have hDef : DefinableSetOf S.Definable (eventuallyAboveSet f a b) :=
    definable_eventuallyAboveSet (S := S) (f := f) (a := a) (b := b) hf
  rcases definable_subset_real_finite_or_contains_Ioo (S := S) hDef with hfin | ⟨u, v, huv, hsub⟩
  · exact hfin
  · exfalso
    exact not_locPattern_pp_on_Ioo_of_strictMonoOn huv
      (strictMonoOn_of_subset_eventuallyAboveSet hsub)
      (fun x hx => locPattern_restrict_Ioo (hpat x (hsub hx).1) hx)

/-- If every point of an interval satisfies `Φ+,+`, then the leftward analogue of Coste's set `B`
is finite there. -/
theorem finite_eventuallyBelowSet_of_locPattern_pp_on_Ioo
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pp f a b x) :
    (eventuallyBelowSet f a b).Finite := by
  have hDef : DefinableSetOf S.Definable (eventuallyBelowSet f a b) :=
    definable_eventuallyBelowSet (S := S) (f := f) (a := a) (b := b) hf
  rcases definable_subset_real_finite_or_contains_Ioo (S := S) hDef with hfin | ⟨u, v, huv, hsub⟩
  · exact hfin
  · exfalso
    exact not_locPattern_pp_on_Ioo_of_strictAntiOn huv
      (strictAntiOn_of_subset_eventuallyBelowSet hsub)
      (fun x hx => locPattern_restrict_Ioo (hpat x (hsub hx).1) hx)

/-- On an injective interval, a point outside Coste's set `B` admits a strictly lower value on its
right. This is Coste's property `(*)` before shrinking away from the finite set `B`. -/
theorem exists_dropRight_of_not_mem_eventuallyAboveSet_of_injOn
    {f : ℝ → ℝ} {a b x : ℝ}
    (hinj : Set.InjOn f (Set.Ioo a b)) (hx : x ∈ Set.Ioo a b)
    (hxB : x ∉ eventuallyAboveSet f a b) :
    ∃ y ∈ Set.Ioo a b, x < y ∧ f y < f x := by
  by_contra hdrop
  have hB : x ∈ eventuallyAboveSet f a b := by
    refine ⟨hx, ?_⟩
    intro y hy hxy
    have hnotlt : ¬ f y < f x := by
      intro hylt
      exact hdrop ⟨y, hy, hxy, hylt⟩
    have hneq : f y ≠ f x := by
      intro hEq
      exact ne_of_lt hxy (hinj hy hx hEq).symm
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact False.elim (hnotlt hlt)
    · exact hgt
  exact hxB hB

/-- On an injective interval, a point outside the leftward analogue of Coste's set `B` admits a
strictly lower value on its left. -/
theorem exists_dropLeft_of_not_mem_eventuallyBelowSet_of_injOn
    {f : ℝ → ℝ} {a b x : ℝ}
    (hinj : Set.InjOn f (Set.Ioo a b)) (hx : x ∈ Set.Ioo a b)
    (hxB : x ∉ eventuallyBelowSet f a b) :
    ∃ y ∈ Set.Ioo a b, y < x ∧ f y < f x := by
  by_contra hdrop
  have hB : x ∈ eventuallyBelowSet f a b := by
    refine ⟨hx, ?_⟩
    intro y hy hyx
    have hnotlt : ¬ f y < f x := by
      intro hylt
      exact hdrop ⟨y, hy, hyx, hylt⟩
    have hneq : f y ≠ f x := by
      intro hEq
      exact ne_of_lt hyx (hinj hy hx hEq)
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact False.elim (hnotlt hlt)
    · exact hgt
  exact hxB hB

/-- On an injective interval where `Φ+,+` holds everywhere, only finitely many points fail to have
a strict right-drop witness. -/
theorem exists_dropRight_on_Ioo_outside_finite_of_locPattern_pp_on_Ioo_and_injOn
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hinj : Set.InjOn f (Set.Ioo a b))
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pp f a b x) :
    ∃ bad : Finset ℝ,
      ∀ x ∈ Set.Ioo a b, x ∉ (bad : Set ℝ) →
        ∃ y ∈ Set.Ioo a b, x < y ∧ f y < f x := by
  let hfin : (eventuallyAboveSet f a b).Finite :=
    finite_eventuallyAboveSet_of_locPattern_pp_on_Ioo (S := S) (f := f) (a := a) (b := b) hf hpat
  refine ⟨hfin.toFinset, ?_⟩
  intro x hx hxbad
  have hxB : x ∉ eventuallyAboveSet f a b := by
    intro hxmem
    exact hxbad (by simpa using hxmem)
  exact exists_dropRight_of_not_mem_eventuallyAboveSet_of_injOn hinj hx hxB

/-- On an injective interval where `Φ+,+` holds everywhere, only finitely many points fail to have
a strict left-drop witness. -/
theorem exists_dropLeft_on_Ioo_outside_finite_of_locPattern_pp_on_Ioo_and_injOn
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hinj : Set.InjOn f (Set.Ioo a b))
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pp f a b x) :
    ∃ bad : Finset ℝ,
      ∀ x ∈ Set.Ioo a b, x ∉ (bad : Set ℝ) →
        ∃ y ∈ Set.Ioo a b, y < x ∧ f y < f x := by
  let hfin : (eventuallyBelowSet f a b).Finite :=
    finite_eventuallyBelowSet_of_locPattern_pp_on_Ioo (S := S) (f := f) (a := a) (b := b) hf hpat
  refine ⟨hfin.toFinset, ?_⟩
  intro x hx hxbad
  have hxB : x ∉ eventuallyBelowSet f a b := by
    intro hxmem
    exact hxbad (by simpa using hxmem)
  exact exists_dropLeft_of_not_mem_eventuallyBelowSet_of_injOn hinj hx hxB

/-- Coste's property `(*)` forces every right-drop set `C_x` to be infinite: otherwise its
maximum would contradict `(*)` at that maximum point. -/
theorem dropRightSet_infinite_of_rightDrop_everywhere
    {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hstar : ∀ y ∈ Set.Ioo a b, ∃ z ∈ Set.Ioo a b, y < z ∧ f z < f y) :
    (dropRightSet f a b x).Infinite := by
  have hne : (dropRightSet f a b x).Nonempty := by
    rcases hstar x hx with ⟨y, hy, hxy, hylt⟩
    exact ⟨y, hy, hxy, hylt⟩
  by_contra hInf
  have hfin : (dropRightSet f a b x).Finite := Set.not_infinite.mp hInf
  obtain ⟨y, hyCx, hymax⟩ := Set.Finite.subset_interval_has_max hfin hne
  rcases hstar y hyCx.1 with ⟨z, hzIoo, hyz, hzy⟩
  have hzCx : z ∈ dropRightSet f a b x := by
    refine ⟨hzIoo, lt_trans hyCx.2.1 hyz, ?_⟩
    exact lt_trans hzy hyCx.2.2
  have hzle : z ≤ y := hymax z hzCx
  exact (not_le_of_gt hyz) hzle

/-- Under Coste's property `(*)`, every right-drop set `C_x` has nonempty witness-based
interior. -/
theorem dropRightInteriorSet_nonempty_of_rightDrop_everywhere
    {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hx : x ∈ Set.Ioo a b)
    (hstar : ∀ y ∈ Set.Ioo a b, ∃ z ∈ Set.Ioo a b, y < z ∧ f z < f y) :
    (dropRightInteriorSet f a b x).Nonempty := by
  have hInf : (dropRightSet f a b x).Infinite :=
    dropRightSet_infinite_of_rightDrop_everywhere hx hstar
  rcases exists_Ioo_subset_dropRightSet_of_infinite (S := S) (f := f) (a := a) (b := b)
      (x := x) hf hInf with ⟨u, v, huv, hsub⟩
  exact dropRightInteriorSet_nonempty_of_exists_Ioo_subset huv hsub

/-- Under Coste's property `(*)`, every right-drop set `C_x` on the ambient interval has
nonempty witness-based interior. -/
theorem dropRightInteriorSet_nonempty_on_Ioo_of_rightDrop_everywhere
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hstar : ∀ y ∈ Set.Ioo a b, ∃ z ∈ Set.Ioo a b, y < z ∧ f z < f y) :
    ∀ x ∈ Set.Ioo a b, (dropRightInteriorSet f a b x).Nonempty := by
  intro x hx
  exact dropRightInteriorSet_nonempty_of_rightDrop_everywhere
    (S := S) (f := f) (a := a) (b := b) (x := x) hf hx hstar

/-- If `Φ+,+` holds on an injective interval, we may shrink to a tail subinterval on which
Coste's property `(*)` holds everywhere. -/
theorem exists_tail_rightDrop_everywhere_of_locPattern_pp_on_Ioo_and_injOn
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hinj : Set.InjOn f (Set.Ioo a b))
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pp f a b x) :
    ∃ c, a ≤ c ∧ c < b ∧
      ∀ x ∈ Set.Ioo c b, ∃ y ∈ Set.Ioo c b, x < y ∧ f y < f x := by
  let B : Set ℝ := eventuallyAboveSet f a b
  have hBfin : B.Finite :=
    finite_eventuallyAboveSet_of_locPattern_pp_on_Ioo (S := S) (f := f) (a := a) (b := b) hf hpat
  by_cases hBne : B.Nonempty
  · obtain ⟨c, hcB, hcmax⟩ := Set.Finite.subset_interval_has_max hBfin hBne
    refine ⟨c, le_of_lt hcB.1.1, hcB.1.2, ?_⟩
    intro x hx
    have hxIoo : x ∈ Set.Ioo a b := ⟨lt_of_le_of_lt (le_of_lt hcB.1.1) hx.1, hx.2⟩
    have hxB : x ∉ B := by
      intro hxmem
      have hxle : x ≤ c := hcmax x hxmem
      exact not_le_of_gt hx.1 hxle
    rcases exists_dropRight_of_not_mem_eventuallyAboveSet_of_injOn
        (f := f) (a := a) (b := b) hinj hxIoo hxB with ⟨y, hyIoo, hxy, hylt⟩
    refine ⟨y, ⟨lt_trans hx.1 hxy, hyIoo.2⟩, hxy, hylt⟩
  · refine ⟨a, le_rfl, hab, ?_⟩
    intro x hx
    have hxB : x ∉ B := by
      intro hxmem
      exact hBne ⟨x, hxmem⟩
    simpa [B] using
      (exists_dropRight_of_not_mem_eventuallyAboveSet_of_injOn
        (f := f) (a := a) (b := b) hinj hx hxB)

/-- If `Φ+,+` holds on an injective interval, we may shrink to a head subinterval on which the
leftward analogue of Coste's property `(*)` holds everywhere. -/
theorem exists_head_leftDrop_everywhere_of_locPattern_pp_on_Ioo_and_injOn
    {S : OMinStructure} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f)
    (hinj : Set.InjOn f (Set.Ioo a b))
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pp f a b x) :
    ∃ c, a < c ∧ c ≤ b ∧
      ∀ x ∈ Set.Ioo a c, ∃ y ∈ Set.Ioo a c, y < x ∧ f y < f x := by
  let B : Set ℝ := eventuallyBelowSet f a b
  have hBfin : B.Finite :=
    finite_eventuallyBelowSet_of_locPattern_pp_on_Ioo (S := S) (f := f) (a := a) (b := b) hf hpat
  by_cases hBne : B.Nonempty
  · obtain ⟨c, hcB, hcmin⟩ := Set.Finite.subset_interval_has_min hBfin hBne
    refine ⟨c, hcB.1.1, le_of_lt hcB.1.2, ?_⟩
    intro x hx
    have hxIoo : x ∈ Set.Ioo a b := ⟨hx.1, lt_trans hx.2 hcB.1.2⟩
    have hxB : x ∉ B := by
      intro hxmem
      have hcle : c ≤ x := hcmin x hxmem
      exact not_le_of_gt hx.2 hcle
    rcases exists_dropLeft_of_not_mem_eventuallyBelowSet_of_injOn
        (f := f) (a := a) (b := b) hinj hxIoo hxB with ⟨y, hyIoo, hyx, hylt⟩
    refine ⟨y, ⟨hyIoo.1, lt_trans hyx hx.2⟩, hyx, hylt⟩
  · refine ⟨b, hab, le_rfl, ?_⟩
    intro x hx
    have hxB : x ∉ B := by
      intro hxmem
      exact hBne ⟨x, hxmem⟩
    simpa [B] using
      (exists_dropLeft_of_not_mem_eventuallyBelowSet_of_injOn
        (f := f) (a := a) (b := b) hinj hx hxB)

/-- Crossing patterns `Ψ` from Coste's proof: points on the left and right of `x` are compared
directly, rather than against `f x`. -/
def CrossPattern (f : ℝ → ℝ) (a b : ℝ) (l r : LocalSign) (x : ℝ) : Prop :=
  ∃ ε > 0,
    Set.Ioo (x - ε) (x + ε) ⊆ Set.Ioo a b ∧
    ∀ t u, x - ε < t → t < x → x < u → u < x + ε →
      match l, r with
      | .plus, .minus => f t > f u
      | .minus, .plus => f t < f u
      | .plus, .plus => f t > f u
      | .minus, .minus => f t < f u

/-- `Ψ+,−` in Coste's notation. -/
abbrev crossPattern_pm (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  CrossPattern f a b .plus .minus x

/-- `Ψ−,+` in Coste's notation. -/
abbrev crossPattern_mp (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  CrossPattern f a b .minus .plus x

/-- A left-right value barrier around `x` yields Coste's pattern `Ψ+,−`. -/
theorem crossPattern_pm_of_value_barrier {f : ℝ → ℝ} {a b x c ε : ℝ}
    (hεpos : 0 < ε) (hsub : Set.Ioo (x - ε) (x + ε) ⊆ Set.Ioo a b)
    (hleft : ∀ t, x - ε < t → t < x → f t > c)
    (hright : ∀ u, x < u → u < x + ε → f u < c) :
    crossPattern_pm f a b x := by
  refine ⟨ε, hεpos, hsub, ?_⟩
  intro t u ht1 ht2 hu1 hu2
  exact gt_trans (hleft t ht1 ht2) (hright u hu1 hu2)

/-- A left-right value barrier around `x` yields Coste's pattern `Ψ−,+`. -/
theorem crossPattern_mp_of_value_barrier {f : ℝ → ℝ} {a b x c ε : ℝ}
    (hεpos : 0 < ε) (hsub : Set.Ioo (x - ε) (x + ε) ⊆ Set.Ioo a b)
    (hleft : ∀ t, x - ε < t → t < x → f t < c)
    (hright : ∀ u, x < u → u < x + ε → c < f u) :
    crossPattern_mp f a b x := by
  refine ⟨ε, hεpos, hsub, ?_⟩
  intro t u ht1 ht2 hu1 hu2
  exact lt_trans (hleft t ht1 ht2) (hright u hu1 hu2)

/-- `Ψ+,−` and `Ψ−,+` cannot hold simultaneously at the same point. -/
theorem not_crossPattern_pm_and_mp_at_point {f : ℝ → ℝ} {a b x : ℝ}
    (hpm : crossPattern_pm f a b x) (hmp : crossPattern_mp f a b x) :
    False := by
  rcases hpm with ⟨ε₁, hε₁pos, -, hpm⟩
  rcases hmp with ⟨ε₂, hε₂pos, -, hmp⟩
  let ε : ℝ := min ε₁ ε₂ / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hmin : 0 < min ε₁ ε₂ := lt_min hε₁pos hε₂pos
  have hhalf_lt_min : min ε₁ ε₂ / 2 < min ε₁ ε₂ := by
    simpa [one_div] using half_lt_self hmin
  have hhalf_lt_ε₁ : min ε₁ ε₂ / 2 < ε₁ :=
    lt_of_lt_of_le hhalf_lt_min (min_le_left _ _)
  have hhalf_lt_ε₂ : min ε₁ ε₂ / 2 < ε₂ :=
    lt_of_lt_of_le hhalf_lt_min (min_le_right _ _)
  let t : ℝ := x - ε
  let u : ℝ := x + ε
  have ht₁ : x - ε₁ < t := by
    dsimp [t, ε]
    linarith
  have ht₂ : t < x := by
    dsimp [t, ε]
    exact sub_lt_self _ hεpos
  have hu₁ : x < u := by
    dsimp [u, ε]
    exact lt_add_of_pos_right _ hεpos
  have hu₂ : u < x + ε₁ := by
    dsimp [u, ε]
    linarith
  have ht₁' : x - ε₂ < t := by
    dsimp [t, ε]
    linarith
  have hu₂' : u < x + ε₂ := by
    dsimp [u, ε]
    linarith
  have hgt : f t > f u := hpm t u ht₁ ht₂ hu₁ hu₂
  have hlt : f t < f u := hmp t u ht₁' ht₂ hu₁ hu₂'
  exact (not_lt_of_gt hgt) hlt

/-- If `Ψ+,−` holds everywhere on a nonempty interval, then `Ψ−,+` cannot also hold everywhere on
that interval. -/
theorem not_crossPattern_mp_on_Ioo_of_crossPattern_pm_on_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hpm : ∀ x ∈ Set.Ioo a b, crossPattern_pm f a b x)
    (hmp : ∀ x ∈ Set.Ioo a b, crossPattern_mp f a b x) :
    False := by
  obtain ⟨x, hx⟩ := exists_between hab
  exact not_crossPattern_pm_and_mp_at_point (hpm x hx) (hmp x hx)

/-- The rightward set used in Coste's least-upper-bound argument for `Φ−,+`. -/
def rightAboveSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ x < y ∧ ∀ z ∈ Set.Ioc x y, f z > f x}

@[simp] theorem mem_rightAboveSet {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ rightAboveSet f a b x ↔
      y ∈ Set.Ioo a b ∧ x < y ∧ ∀ z ∈ Set.Ioc x y, f z > f x := Iff.rfl

/-- The leftward set used in the symmetric one-sided interval arguments. -/
def leftAboveSet (f : ℝ → ℝ) (a b x : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Ioo a b ∧ y < x ∧ ∀ z ∈ Set.Ico y x, f z > f x}

@[simp] theorem mem_leftAboveSet {f : ℝ → ℝ} {a b x y : ℝ} :
    y ∈ leftAboveSet f a b x ↔
      y ∈ Set.Ioo a b ∧ y < x ∧ ∀ z ∈ Set.Ico y x, f z > f x := Iff.rfl

/-- The left-above set is definable once the base point lies in the definability interval. -/
theorem definable_leftAboveSet {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) (hx : x ∈ Set.Ioo a b) :
    DefinableSetOf S.Definable (leftAboveSet f a b x) := by
  have hBad : DefinableSetOf S.Definable (badLeftAboveSet f a b x) :=
    definable_badLeftAboveSet (S := S) (f := f) (a := a) (b := b) (x := x) hf
  have hEq : leftAboveSet f a b x = (Set.Ioo a b ∩ Set.Iio x) ∩ (badLeftAboveSet f a b x)ᶜ := by
    ext y
    constructor
    · intro hy
      refine ⟨⟨hy.1, hy.2.1⟩, ?_⟩
      intro hyBad
      rcases hyBad with ⟨-, z, hzNonRise, hyz⟩
      have hzIco : z ∈ Set.Ico y x := ⟨hyz, hzNonRise.2.1⟩
      exact hzNonRise.2.2 (hy.2.2 z hzIco)
    · rintro ⟨⟨hyI, hyx⟩, hyBad⟩
      refine ⟨hyI, hyx, ?_⟩
      intro z hz
      by_contra hnotgt
      have hzI : z ∈ Set.Ioo a b := by
        refine ⟨lt_of_lt_of_le hyI.1 hz.1, lt_trans hz.2 hx.2⟩
      have hzNonRise : z ∈ nonRiseToSet f a b x := ⟨hzI, hz.2, by simpa using hnotgt⟩
      exact hyBad ⟨hyI, z, hzNonRise, hz.1⟩
  have hIoo : S.Definable (encodeSet ℝ (Set.Ioo a b)) := by
    simpa [DefinableSetOf] using S.definableIoo a b
  have hIio : S.Definable (encodeSet ℝ (Set.Iio x)) := by
    simpa [DefinableSetOf] using S.definableIio x
  have hBadRaw : S.Definable (encodeSet ℝ (badLeftAboveSet f a b x)) := by
    simpa [DefinableSetOf] using hBad
  simpa [DefinableSetOf, hEq] using
    S.definable_inter (S.definable_inter hIoo hIio) (S.definable_compl hBadRaw)

/-- The right-above set is definable once the base point lies in the definability interval. -/
theorem definable_rightAboveSet {S : OMinStructure} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DefinableMapOf S.Definable (Set.Ioo a b) f) (hx : x ∈ Set.Ioo a b) :
    DefinableSetOf S.Definable (rightAboveSet f a b x) := by
  have hBad : DefinableSetOf S.Definable (badRightAboveSet f a b x) :=
    definable_badRightAboveSet (S := S) (f := f) (a := a) (b := b) (x := x) hf
  have hEq : rightAboveSet f a b x = (Set.Ioo a b ∩ Set.Ioi x) ∩ (badRightAboveSet f a b x)ᶜ := by
    ext y
    constructor
    · intro hy
      refine ⟨⟨hy.1, hy.2.1⟩, ?_⟩
      intro hyBad
      rcases hyBad with ⟨-, z, hzNonRise, hzy⟩
      have hzIoc : z ∈ Set.Ioc x y := ⟨hzNonRise.2.1, hzy⟩
      exact hzNonRise.2.2 (hy.2.2 z hzIoc)
    · rintro ⟨⟨hyI, hxy⟩, hyBad⟩
      refine ⟨hyI, hxy, ?_⟩
      intro z hz
      by_contra hnotgt
      have hzI : z ∈ Set.Ioo a b := by
        refine ⟨lt_trans hx.1 hz.1, lt_of_le_of_lt hz.2 hyI.2⟩
      have hzNonRise : z ∈ nonRiseFromSet f a b x := ⟨hzI, hz.1, by simpa using hnotgt⟩
      exact hyBad ⟨hyI, z, hzNonRise, hz.2⟩
  have hIoo : S.Definable (encodeSet ℝ (Set.Ioo a b)) := by
    simpa [DefinableSetOf] using S.definableIoo a b
  have hIoi : S.Definable (encodeSet ℝ (Set.Ioi x)) := by
    simpa [DefinableSetOf] using S.definableIoi x
  have hBadRaw : S.Definable (encodeSet ℝ (badRightAboveSet f a b x)) := by
    simpa [DefinableSetOf] using hBad
  simpa [DefinableSetOf, hEq] using
    S.definable_inter (S.definable_inter hIoo hIoi) (S.definable_compl hBadRaw)

/-- The positive right-sign witness set is exactly Coste's `rightAboveSet`. -/
theorem rightSignSet_plus_eq_rightAboveSet {f : ℝ → ℝ} {a b x : ℝ} :
    rightSignSet .plus f a b x = rightAboveSet f a b x := by
  ext y
  simp [rightSignSet, rightAboveSet, localSignRel_plus]

/-- The positive left-sign witness set is exactly `leftAboveSet`. -/
theorem leftSignSet_plus_eq_leftAboveSet {f : ℝ → ℝ} {a b x : ℝ} :
    leftSignSet .plus f a b x = leftAboveSet f a b x := by
  ext y
  simp [leftSignSet, leftAboveSet, localSignRel_plus]

/-- The negative left-sign witness set is the positive one for the negated function. -/
theorem leftSignSet_minus_eq_leftAboveSet_neg {f : ℝ → ℝ} {a b x : ℝ} :
    leftSignSet .minus f a b x = leftAboveSet (fun t => -f t) a b x := by
  ext y
  constructor
  · rintro ⟨hyI, hyx, hy⟩
    refine ⟨hyI, hyx, ?_⟩
    intro z hz
    have hzlt : f z < f x := hy z hz
    exact neg_lt_neg hzlt
  · rintro ⟨hyI, hyx, hy⟩
    refine ⟨hyI, hyx, ?_⟩
    intro z hz
    have hzgt : -f z > -f x := hy z hz
    exact neg_lt_neg_iff.mp hzgt

/-- The negative right-sign witness set is the positive one for the negated function. -/
theorem rightSignSet_minus_eq_rightAboveSet_neg {f : ℝ → ℝ} {a b x : ℝ} :
    rightSignSet .minus f a b x = rightAboveSet (fun t => -f t) a b x := by
  ext y
  constructor
  · rintro ⟨hyI, hxy, hy⟩
    refine ⟨hyI, hxy, ?_⟩
    intro z hz
    have hzlt : f z < f x := hy z hz
    exact neg_lt_neg hzlt
  · rintro ⟨hyI, hxy, hy⟩
    refine ⟨hyI, hxy, ?_⟩
    intro z hz
    have hzgt : -f z > -f x := hy z hz
    exact neg_lt_neg_iff.mp hzgt

/-- `Φ+,+` at `x` gives an initial interval of points to the right of `x` that lie in
`rightAboveSet f a b x`. -/
theorem exists_Ioo_subset_rightAboveSet_of_locPattern_pp {f : ℝ → ℝ} {a b x : ℝ}
    (hpat : locPattern_pp f a b x) :
    ∃ u, x < u ∧ u ∈ Set.Ioo a b ∧ Set.Ioo x u ⊆ rightAboveSet f a b x := by
  rcases hpat with ⟨ε, hεpos, hsub, -, hright⟩
  let u : ℝ := x + ε / 2
  have hxu : x < u := by
    dsimp [u]
    linarith
  have huε : u < x + ε := by
    dsimp [u]
    linarith
  have huI : u ∈ Set.Ioo a b := hsub ⟨by dsimp [u]; linarith, huε⟩
  refine ⟨u, hxu, huI, ?_⟩
  intro y hy
  have hy_left : x - ε < y := lt_trans (by linarith : x - ε < x) hy.1
  have hyI : y ∈ Set.Ioo a b := hsub ⟨hy_left, lt_trans hy.2 huε⟩
  refine ⟨hyI, hy.1, ?_⟩
  intro z hz
  exact hright z hz.1 (lt_of_le_of_lt hz.2 (lt_trans hy.2 huε))

/-- In particular, `rightAboveSet f a b x` is nonempty whenever `Φ+,+` holds at `x`. -/
theorem rightAboveSet_nonempty_of_locPattern_pp {f : ℝ → ℝ} {a b x : ℝ}
    (hpat : locPattern_pp f a b x) :
    (rightAboveSet f a b x).Nonempty := by
  rcases exists_Ioo_subset_rightAboveSet_of_locPattern_pp hpat with ⟨u, hxu, -, hsub⟩
  rcases exists_between hxu with ⟨t, ht⟩
  exact ⟨t, hsub ht⟩

/-- `rightAboveSet` is downward closed above `x`. -/
theorem mem_rightAboveSet_of_lt_of_mem {f : ℝ → ℝ} {a b x y t : ℝ}
    (hyI : y ∈ Set.Ioo a b) (hxy : x < y) (hyt : y < t) (ht : t ∈ rightAboveSet f a b x) :
    y ∈ rightAboveSet f a b x := by
  refine ⟨hyI, hxy, ?_⟩
  intro z hz
  exact ht.2.2 z ⟨hz.1, le_trans hz.2 hyt.le⟩

/-- Every point strictly between `x` and the supremum of the right-above set still belongs to that
set. -/
theorem mem_rightAboveSet_of_lt_csSup {f : ℝ → ℝ} {a b x t : ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hDnonempty : (rightAboveSet f a b x).Nonempty)
    (hDbdd : BddAbove (rightAboveSet f a b x))
    (hsSup_le_b : sSup (rightAboveSet f a b x) ≤ b)
    (hxt : x < t) (hts : t < sSup (rightAboveSet f a b x)) :
    t ∈ rightAboveSet f a b x := by
  obtain ⟨u, huD, htu⟩ : ∃ u ∈ rightAboveSet f a b x, t < u := by
    exact (lt_csSup_iff hDbdd hDnonempty).1 hts
  have htI : t ∈ Set.Ioo a b := by
    refine ⟨lt_trans hx.1 hxt, lt_of_lt_of_le hts hsSup_le_b⟩
  exact mem_rightAboveSet_of_lt_of_mem htI hxt htu huD

/-- Any point of `C_x` is an upper bound for the right-above set, so the supremum of the latter
lies to its left. -/
theorem csSup_rightAboveSet_le_of_mem_dropRightSet {f : ℝ → ℝ} {a b x y : ℝ}
    (hDnonempty : (rightAboveSet f a b x).Nonempty)
    (hDbdd : BddAbove (rightAboveSet f a b x))
    (hy : y ∈ dropRightSet f a b x) :
    sSup (rightAboveSet f a b x) ≤ y := by
  have hyUb : ∀ t ∈ rightAboveSet f a b x, t ≤ y := by
    intro t ht
    by_contra hyt
    have hyt' : y < t := lt_of_not_ge hyt
    have hyIoc : y ∈ Set.Ioc x t := ⟨hy.2.1, hyt'.le⟩
    exact (not_lt_of_ge hy.2.2.le) (ht.2.2 y hyIoc)
  exact (csSup_le_iff hDbdd hDnonempty).2 hyUb

/-- No point strictly to the right of the supremum of the right-above set belongs to that set. -/
theorem not_mem_rightAboveSet_of_csSup_lt {f : ℝ → ℝ} {a b x y : ℝ}
    (hDbdd : BddAbove (rightAboveSet f a b x))
    (hy : sSup (rightAboveSet f a b x) < y) :
    y ∉ rightAboveSet f a b x := by
  intro hyD
  exact (not_le_of_gt hy) (le_csSup hDbdd hyD)

/-- `Φ+,+` at `x` implies that the supremum of the right-above set lies strictly to the right of
`x`. -/
theorem x_lt_csSup_rightAboveSet_of_locPattern_pp {f : ℝ → ℝ} {a b x : ℝ}
    (hpat : locPattern_pp f a b x) :
    x < sSup (rightAboveSet f a b x) := by
  have hDnonempty : (rightAboveSet f a b x).Nonempty :=
    rightAboveSet_nonempty_of_locPattern_pp hpat
  have hDbdd : BddAbove (rightAboveSet f a b x) := ⟨b, by intro t ht; exact ht.1.2.le⟩
  rcases hDnonempty with ⟨u, hu⟩
  exact lt_of_lt_of_le hu.2.1 (le_csSup hDbdd hu)

/-- Every point of the witness-based interior of `C_x` lies strictly to the right of the supremum
of the right-above set. -/
theorem csSup_rightAboveSet_lt_of_mem_dropRightInteriorSet
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hDnonempty : (rightAboveSet f a b x).Nonempty)
    (hDbdd : BddAbove (rightAboveSet f a b x))
    (hz : z ∈ dropRightInteriorSet f a b x) :
    sSup (rightAboveSet f a b x) < z := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  let y : ℝ := (u + z) / 2
  have huy : u < y := by
    dsimp [y]
    linarith [hzuv.1]
  have hy_lt_z : y < z := by
    dsimp [y]
    linarith [hzuv.1]
  have hyuv : y ∈ Set.Ioo u v := by
    constructor
    · exact huy
    · exact lt_trans hy_lt_z hzuv.2
  have hyDrop : y ∈ dropRightSet f a b x := hsub hyuv
  have hsSup_le_y : sSup (rightAboveSet f a b x) ≤ y :=
    csSup_rightAboveSet_le_of_mem_dropRightSet hDnonempty hDbdd hyDrop
  exact lt_of_le_of_lt hsSup_le_y hy_lt_z

/-- In particular, under `Φ+,+`, every point of the witness-based interior of `C_x` lies strictly
to the right of `x`. -/
theorem x_lt_mem_dropRightInteriorSet_of_locPattern_pp
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hpat : locPattern_pp f a b x)
    (hz : z ∈ dropRightInteriorSet f a b x) :
    x < z := by
  have hDnonempty : (rightAboveSet f a b x).Nonempty :=
    rightAboveSet_nonempty_of_locPattern_pp hpat
  have hDbdd : BddAbove (rightAboveSet f a b x) := ⟨b, by intro t ht; exact ht.1.2.le⟩
  exact lt_trans (x_lt_csSup_rightAboveSet_of_locPattern_pp hpat)
    (csSup_rightAboveSet_lt_of_mem_dropRightInteriorSet hDnonempty hDbdd hz)

/-- If `Φ+,+` holds at `x` and there is some point of `C_x`, then just to the left of
`sSup (rightAboveSet f a b x)` the function is strictly above `f x`. -/
theorem exists_left_value_barrier_at_csSup_rightAboveSet_of_locPattern_pp_of_mem_dropRightSet
    {f : ℝ → ℝ} {a b x y : ℝ}
    (hpat : locPattern_pp f a b x) (hy : y ∈ dropRightSet f a b x) :
    ∃ ε > 0,
      Set.Ioo (sSup (rightAboveSet f a b x) - ε) (sSup (rightAboveSet f a b x)) ⊆ Set.Ioo a b ∧
      ∀ t, sSup (rightAboveSet f a b x) - ε < t →
        t < sSup (rightAboveSet f a b x) → f t > f x := by
  let D := rightAboveSet f a b x
  have hx : x ∈ Set.Ioo a b := mem_Ioo_of_locPattern hpat
  have hDnonempty : D.Nonempty := by
    simpa [D] using rightAboveSet_nonempty_of_locPattern_pp hpat
  have hDbdd : BddAbove D := ⟨b, by intro t ht; exact ht.1.2.le⟩
  have hx_lt_sSup : x < sSup D := by
    rcases hDnonempty with ⟨u, hu⟩
    exact lt_of_lt_of_le hu.2.1 (le_csSup hDbdd hu)
  have hsSup_le_b : sSup D ≤ b := by
    exact (csSup_le_iff hDbdd hDnonempty).2 (fun t ht => ht.1.2.le)
  have hsSup_le_y : sSup D ≤ y := by
    simpa [D] using
      csSup_rightAboveSet_le_of_mem_dropRightSet (hDnonempty := hDnonempty) (hDbdd := hDbdd) hy
  have hsSup_lt_b : sSup D < b := lt_of_le_of_lt hsSup_le_y hy.1.2
  have hsSupI : sSup D ∈ Set.Ioo x b := ⟨hx_lt_sSup, hsSup_lt_b⟩
  rcases exists_small_Ioo_around_mem_Ioo (a := x) (b := b) (x := sSup D) hsSupI with
    ⟨ε, hεpos, hεsub⟩
  refine ⟨ε, hεpos, ?_, ?_⟩
  · intro t ht
    have htxb : t ∈ Set.Ioo x b := hεsub ⟨ht.1, lt_trans ht.2 (by linarith)⟩
    exact ⟨lt_trans hx.1 htxb.1, htxb.2⟩
  · intro t ht1 ht2
    have htxb : t ∈ Set.Ioo x b := hεsub ⟨ht1, lt_trans ht2 (by linarith)⟩
    have htD : t ∈ D := by
      exact mem_rightAboveSet_of_lt_csSup hx hDnonempty hDbdd hsSup_le_b htxb.1 ht2
    exact htD.2.2 t ⟨htD.2.1, le_rfl⟩

/-- If the left endpoint of an interval contained in `C_x` matches the supremum of
`rightAboveSet f a b x`, then that endpoint satisfies `Ψ+,−`. -/
theorem crossPattern_pm_of_locPattern_pp_of_Ioo_subset_dropRightSet_and_csSup_eq_left
    {f : ℝ → ℝ} {a b x u v : ℝ}
    (hpat : locPattern_pp f a b x)
    (huv : u < v)
    (hdrop : Set.Ioo u v ⊆ dropRightSet f a b x)
    (hsSup : sSup (rightAboveSet f a b x) = u) :
    crossPattern_pm f a b u := by
  let y : ℝ := (u + v) / 2
  have hyI : y ∈ Set.Ioo u v := by
    dsimp [y]
    constructor <;> linarith
  have hyDrop : y ∈ dropRightSet f a b x := hdrop hyI
  rcases exists_left_value_barrier_at_csSup_rightAboveSet_of_locPattern_pp_of_mem_dropRightSet
      (f := f) (a := a) (b := b) (x := x) (y := y) hpat hyDrop with
    ⟨ε₁, hε₁pos, hε₁sub, hleft₁⟩
  let ε₂ : ℝ := (v - u) / 2
  have hε₂pos : 0 < ε₂ := by
    dsimp [ε₂]
    linarith
  have huε₂v : u + ε₂ < v := by
    dsimp [ε₂]
    linarith
  let ε : ℝ := min ε₁ ε₂
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hε₁pos hε₂pos
  have hεle₁ : ε ≤ ε₁ := by
    dsimp [ε]
    exact min_le_left _ _
  have hεle₂ : ε ≤ ε₂ := by
    dsimp [ε]
    exact min_le_right _ _
  have huI : u ∈ Set.Ioo a b := by
    let t0 : ℝ := u - ε₁ / 2
    have ht0Int : t0 ∈ Set.Ioo (sSup (rightAboveSet f a b x) - ε₁) (sSup (rightAboveSet f a b x)) := by
      rw [hsSup]
      dsimp [t0]
      constructor <;> linarith
    have ht0I : t0 ∈ Set.Ioo a b := hε₁sub ht0Int
    refine ⟨?_, ?_⟩
    · dsimp [t0] at ht0I
      have ht0ltu : t0 < u := by
        dsimp [t0]
        linarith
      exact lt_trans ht0I.1 ht0ltu
    · exact lt_trans hyI.1 hyDrop.1.2
  refine crossPattern_pm_of_value_barrier (x := u) (c := f x) hεpos ?_ ?_ ?_
  · intro t ht
    by_cases htu : t < u
    · have ht1' : sSup (rightAboveSet f a b x) - ε₁ < t := by
        rw [hsSup]
        have hbound : u - ε₁ ≤ u - ε := by
          linarith
        exact lt_of_le_of_lt hbound ht.1
      have htI : t ∈ Set.Ioo a b := hε₁sub ⟨ht1', by simpa [hsSup] using htu⟩
      exact htI
    · have hute : u ≤ t := le_of_not_gt htu
      rcases eq_or_lt_of_le hute with rfl | hut
      · exact huI
      · have htv : t < v := by
          linarith [ht.2, hεle₂, huε₂v]
        exact (hdrop ⟨hut, htv⟩).1
  · intro t ht1 htu
    have ht1' : sSup (rightAboveSet f a b x) - ε₁ < t := by
      rw [hsSup]
      have hbound : u - ε₁ ≤ u - ε := by
        linarith
      exact lt_of_le_of_lt hbound ht1
    have htu' : t < sSup (rightAboveSet f a b x) := by
      simpa [hsSup] using htu
    exact hleft₁ t ht1' htu'
  · intro w huw hwu
    have hwv : w < v := by
      linarith [hwu, hεle₂, huε₂v]
    exact (hdrop ⟨huw, hwv⟩).2.2

/-- `Φ+,+` at `x` gives a final interval of points to the left of `x` that lie in
`leftAboveSet f a b x`. -/
theorem exists_Ioo_subset_leftAboveSet_of_locPattern_pp {f : ℝ → ℝ} {a b x : ℝ}
    (hpat : locPattern_pp f a b x) :
    ∃ u, u < x ∧ u ∈ Set.Ioo a b ∧ Set.Ioo u x ⊆ leftAboveSet f a b x := by
  rcases hpat with ⟨ε, hεpos, hsub, hleft, -⟩
  let u : ℝ := x - ε / 2
  have hux : u < x := by
    dsimp [u]
    linarith
  have hxu : x - ε < u := by
    dsimp [u]
    linarith
  have huI : u ∈ Set.Ioo a b := hsub ⟨hxu, by
    dsimp [u]
    linarith⟩
  refine ⟨u, hux, huI, ?_⟩
  intro y hy
  have hyI : y ∈ Set.Ioo a b := hsub ⟨lt_trans hxu hy.1, by
    linarith [hy.2, hεpos]⟩
  refine ⟨hyI, hy.2, ?_⟩
  intro z hz
  exact hleft z (lt_of_lt_of_le (lt_trans hxu hy.1) hz.1) hz.2

/-- In particular, `leftAboveSet f a b x` is nonempty whenever `Φ+,+` holds at `x`. -/
theorem leftAboveSet_nonempty_of_locPattern_pp {f : ℝ → ℝ} {a b x : ℝ}
    (hpat : locPattern_pp f a b x) :
    (leftAboveSet f a b x).Nonempty := by
  rcases exists_Ioo_subset_leftAboveSet_of_locPattern_pp hpat with ⟨u, hux, -, hsub⟩
  rcases exists_between hux with ⟨t, ht⟩
  exact ⟨t, hsub ht⟩

/-- `leftAboveSet` is upward closed below `x`. -/
theorem mem_leftAboveSet_of_mem_of_lt {f : ℝ → ℝ} {a b x y t : ℝ}
    (hyI : y ∈ Set.Ioo a b) (hty : t < y) (hyx : y < x) (ht : t ∈ leftAboveSet f a b x) :
    y ∈ leftAboveSet f a b x := by
  refine ⟨hyI, hyx, ?_⟩
  intro z hz
  exact ht.2.2 z ⟨le_trans hty.le hz.1, hz.2⟩

/-- Every point strictly between the infimum of the left-above set and `x` still belongs to that
set. -/
theorem mem_leftAboveSet_of_csInf_lt {f : ℝ → ℝ} {a b x t : ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hDnonempty : (leftAboveSet f a b x).Nonempty)
    (hDbdd : BddBelow (leftAboveSet f a b x))
    (hInf : sInf (leftAboveSet f a b x) < t)
    (htx : t < x) :
    t ∈ leftAboveSet f a b x := by
  obtain ⟨u, huD, hut⟩ : ∃ u ∈ leftAboveSet f a b x, u < t := by
    exact (csInf_lt_iff hDbdd hDnonempty).1 hInf
  have ha_le : a ≤ sInf (leftAboveSet f a b x) := by
    exact le_csInf hDnonempty (by intro z hz; exact hz.1.1.le)
  have htI : t ∈ Set.Ioo a b := by
    refine ⟨lt_of_le_of_lt ha_le hInf, lt_trans htx hx.2⟩
  exact mem_leftAboveSet_of_mem_of_lt htI hut htx huD

/-- Any point of the leftward drop set is a lower bound for the left-above set, so the infimum of
the latter lies to its right. -/
theorem le_csInf_leftAboveSet_of_mem_dropLeftSet {f : ℝ → ℝ} {a b x y : ℝ}
    (hDnonempty : (leftAboveSet f a b x).Nonempty)
    (hy : y ∈ dropLeftSet f a b x) :
    y ≤ sInf (leftAboveSet f a b x) := by
  have hyLower : y ∈ lowerBounds (leftAboveSet f a b x) := by
    intro t ht
    by_contra hyt
    have hty : t < y := lt_of_not_ge hyt
    have hyIco : y ∈ Set.Ico t x := ⟨hty.le, hy.2.1⟩
    exact (not_lt_of_ge hy.2.2.le) (ht.2.2 y hyIco)
  exact le_csInf hDnonempty hyLower

/-- `Φ+,+` at `x` implies that the infimum of the left-above set lies strictly to the left of
`x`. -/
theorem csInf_leftAboveSet_lt_x_of_locPattern_pp {f : ℝ → ℝ} {a b x : ℝ}
    (hpat : locPattern_pp f a b x) :
    sInf (leftAboveSet f a b x) < x := by
  have hDnonempty : (leftAboveSet f a b x).Nonempty :=
    leftAboveSet_nonempty_of_locPattern_pp hpat
  have hDbdd : BddBelow (leftAboveSet f a b x) := ⟨a, by
    intro t ht
    exact ht.1.1.le⟩
  rcases hDnonempty with ⟨u, hu⟩
  exact lt_of_le_of_lt (csInf_le hDbdd hu) hu.2.1

/-- Every point of the witness-based interior of the leftward drop set lies strictly to the left
of the infimum of the left-above set. -/
theorem lt_csInf_leftAboveSet_of_mem_dropLeftInteriorSet
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hDnonempty : (leftAboveSet f a b x).Nonempty)
    (hz : z ∈ dropLeftInteriorSet f a b x) :
    z < sInf (leftAboveSet f a b x) := by
  rcases hz with ⟨u, v, huv, hzuv, hsub⟩
  let y : ℝ := (z + v) / 2
  have hzy : z < y := by
    dsimp [y]
    linarith [hzuv.2]
  have hyv : y < v := by
    dsimp [y]
    linarith [hzuv.2]
  have hyuv : y ∈ Set.Ioo u v := by
    constructor
    · exact lt_trans hzuv.1 hzy
    · exact hyv
  have hyDrop : y ∈ dropLeftSet f a b x := hsub hyuv
  have hy_le : y ≤ sInf (leftAboveSet f a b x) :=
    le_csInf_leftAboveSet_of_mem_dropLeftSet hDnonempty hyDrop
  exact lt_of_lt_of_le hzy hy_le

/-- In particular, under `Φ+,+`, every point of the witness-based interior of the leftward drop
set lies strictly to the left of `x`. -/
theorem mem_dropLeftInteriorSet_lt_x_of_locPattern_pp
    {f : ℝ → ℝ} {a b x z : ℝ}
    (hpat : locPattern_pp f a b x)
    (hz : z ∈ dropLeftInteriorSet f a b x) :
    z < x := by
  have hDnonempty : (leftAboveSet f a b x).Nonempty :=
    leftAboveSet_nonempty_of_locPattern_pp hpat
  exact lt_trans (lt_csInf_leftAboveSet_of_mem_dropLeftInteriorSet hDnonempty hz)
    (csInf_leftAboveSet_lt_x_of_locPattern_pp hpat)

/-- If `Φ+,+` holds at `x` and there is some point of the leftward drop set, then just to the
right of `sInf (leftAboveSet f a b x)` the function is strictly above `f x`. -/
theorem exists_right_value_barrier_at_csInf_leftAboveSet_of_locPattern_pp_of_mem_dropLeftSet
    {f : ℝ → ℝ} {a b x y : ℝ}
    (hpat : locPattern_pp f a b x) (hy : y ∈ dropLeftSet f a b x) :
    ∃ ε > 0,
      Set.Ioo (sInf (leftAboveSet f a b x)) (sInf (leftAboveSet f a b x) + ε) ⊆ Set.Ioo a b ∧
      ∀ t, sInf (leftAboveSet f a b x) < t →
        t < sInf (leftAboveSet f a b x) + ε → f t > f x := by
  let D := leftAboveSet f a b x
  have hx : x ∈ Set.Ioo a b := mem_Ioo_of_locPattern hpat
  have hDnonempty : D.Nonempty := by
    simpa [D] using leftAboveSet_nonempty_of_locPattern_pp hpat
  have hDbdd : BddBelow D := ⟨a, by intro t ht; exact ht.1.1.le⟩
  have hy_le_sInf : y ≤ sInf D := by
    simpa [D] using le_csInf_leftAboveSet_of_mem_dropLeftSet (hDnonempty := hDnonempty) hy
  have ha_lt_sInf : a < sInf D := lt_of_lt_of_le hy.1.1 hy_le_sInf
  have hsInf_lt_x : sInf D < x := by
    simpa [D] using csInf_leftAboveSet_lt_x_of_locPattern_pp hpat
  have hsInfI : sInf D ∈ Set.Ioo a x := ⟨ha_lt_sInf, hsInf_lt_x⟩
  rcases exists_small_Ioo_around_mem_Ioo (a := a) (b := x) (x := sInf D) hsInfI with
    ⟨ε, hεpos, hεsub⟩
  refine ⟨ε, hεpos, ?_, ?_⟩
  · intro t ht
    have htax : t ∈ Set.Ioo a x := hεsub ⟨by linarith [hεpos, ht.1], ht.2⟩
    exact ⟨htax.1, lt_trans htax.2 hx.2⟩
  · intro t ht1 ht2
    have htx : t < x := (hεsub ⟨by linarith [hεpos, ht1], ht2⟩).2
    have htD : t ∈ D := by
      exact mem_leftAboveSet_of_csInf_lt hx hDnonempty hDbdd ht1 htx
    exact htD.2.2 t ⟨le_rfl, htD.2.1⟩

/-- If the right endpoint of an interval contained in the leftward drop set matches the infimum of
`leftAboveSet f a b x`, then that endpoint satisfies `Ψ−,+`. -/
theorem crossPattern_mp_of_locPattern_pp_of_Ioo_subset_dropLeftSet_and_csInf_eq_right
    {f : ℝ → ℝ} {a b x u v : ℝ}
    (hpat : locPattern_pp f a b x)
    (huv : u < v)
    (hdrop : Set.Ioo u v ⊆ dropLeftSet f a b x)
    (hsInf : sInf (leftAboveSet f a b x) = v) :
    crossPattern_mp f a b v := by
  let y : ℝ := (u + v) / 2
  have hyI : y ∈ Set.Ioo u v := by
    dsimp [y]
    constructor <;> linarith
  have hyDrop : y ∈ dropLeftSet f a b x := hdrop hyI
  rcases exists_right_value_barrier_at_csInf_leftAboveSet_of_locPattern_pp_of_mem_dropLeftSet
      (f := f) (a := a) (b := b) (x := x) (y := y) hpat hyDrop with
    ⟨ε₁, hε₁pos, hε₁sub, hright₁⟩
  let ε₂ : ℝ := (v - u) / 2
  have hε₂pos : 0 < ε₂ := by
    dsimp [ε₂]
    linarith
  have huvε₂ : u < v - ε₂ := by
    dsimp [ε₂]
    linarith
  let ε : ℝ := min ε₁ ε₂
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hε₁pos hε₂pos
  have hεle₁ : ε ≤ ε₁ := by
    dsimp [ε]
    exact min_le_left _ _
  have hεle₂ : ε ≤ ε₂ := by
    dsimp [ε]
    exact min_le_right _ _
  have hvI : v ∈ Set.Ioo a b := by
    let t0 : ℝ := v + ε₁ / 2
    have ht0Int : t0 ∈ Set.Ioo (sInf (leftAboveSet f a b x))
        (sInf (leftAboveSet f a b x) + ε₁) := by
      rw [hsInf]
      dsimp [t0]
      constructor <;> linarith
    have ht0I : t0 ∈ Set.Ioo a b := hε₁sub ht0Int
    refine ⟨?_, ?_⟩
    · exact lt_trans hyDrop.1.1 hyI.2
    · have hvt0 : v < t0 := by
        dsimp [t0]
        linarith
      exact lt_trans hvt0 ht0I.2
  refine crossPattern_mp_of_value_barrier (x := v) (c := f x) hεpos ?_ ?_ ?_
  · intro t ht
    by_cases htv : t < v
    · have hut : u < t := by
        have hbound : v - ε₂ ≤ v - ε := by
          linarith
        exact lt_trans huvε₂ (lt_of_le_of_lt hbound ht.1)
      exact (hdrop ⟨hut, htv⟩).1
    · have hvt : v ≤ t := le_of_not_gt htv
      rcases eq_or_lt_of_le hvt with rfl | hvt'
      · exact hvI
      · have htInt : t ∈ Set.Ioo (sInf (leftAboveSet f a b x))
            (sInf (leftAboveSet f a b x) + ε₁) := by
          rw [hsInf]
          constructor
          · exact hvt'
          · linarith [ht.2, hεle₁]
        exact hε₁sub htInt
  · intro t htv htv'
    have hut : u < t := by
      have hbound : v - ε₂ ≤ v - ε := by
        linarith
      exact lt_trans huvε₂ (lt_of_le_of_lt hbound htv)
    exact (hdrop ⟨hut, htv'⟩).2.2
  · intro w hvw hwv
    have hwInt : w ∈ Set.Ioo (sInf (leftAboveSet f a b x))
        (sInf (leftAboveSet f a b x) + ε₁) := by
      rw [hsInf]
      constructor
      · exact hvw
      · linarith [hwv, hεle₁]
    exact hright₁ w hwInt.1 hwInt.2

/-- If `Φ−,+` holds at every point of an interval, then the function is strictly increasing there. -/
theorem strictMonoOn_of_locPattern_mp {f : ℝ → ℝ} {a b : ℝ}
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_mp f a b x) :
    StrictMonoOn f (Set.Ioo a b) := by
  intro x hx y hy hxy
  let D := rightAboveSet f a b x
  have hDnonempty : D.Nonempty := by
    rcases hpat x hx with ⟨ε, hεpos, hεsub, -, hright⟩
    let u : ℝ := x + ε / 2
    have hxu : x < u := by
      dsimp [u]
      linarith
    have huε : u < x + ε := by
      dsimp [u]
      linarith
    have huI : u ∈ Set.Ioo a b := hεsub ⟨by dsimp [u]; linarith, huε⟩
    refine ⟨u, huI, hxu, ?_⟩
    intro z hz
    exact hright z hz.1 (lt_of_le_of_lt hz.2 huε)
  have hDbdd : BddAbove D := ⟨b, by intro t ht; exact ht.1.2.le⟩
  have hx_lt_sSup : x < sSup D := by
    rcases hDnonempty with ⟨u, hu⟩
    exact lt_of_lt_of_le hu.2.1 (le_csSup hDbdd hu)
  have hsSup_le_b : sSup D ≤ b := by
    exact (csSup_le_iff hDbdd hDnonempty).2 (fun t ht => ht.1.2.le)
  have hsSup_eq_b : sSup D = b := by
    by_contra hsne
    have hsSup_lt_b : sSup D < b := lt_of_le_of_ne hsSup_le_b hsne
    have hsSupI : sSup D ∈ Set.Ioo a b := ⟨lt_trans hx.1 hx_lt_sSup, hsSup_lt_b⟩
    rcases hpat (sSup D) hsSupI with ⟨ε, hεpos, hεsub, hleft, hright⟩
    obtain ⟨w, hwxs, hws⟩ : ∃ w : ℝ, max x (sSup D - ε / 2) < w ∧ w < sSup D := by
      exact exists_between (max_lt_iff.mpr ⟨hx_lt_sSup, by linarith⟩)
    obtain ⟨t, htD, hwt⟩ : ∃ t ∈ D, w < t := by
      exact (lt_csSup_iff hDbdd hDnonempty).1 hws
    have hwI : w ∈ Set.Ioo a b := by
      have htI : t ∈ Set.Ioo a b := htD.1
      refine ⟨?_, ?_⟩
      · have hxw : x < w := lt_of_le_of_lt (le_max_left _ _) hwxs
        exact lt_trans hx.1 hxw
      · exact lt_trans hwt htI.2
    have hwD : w ∈ D := by
      have hxw : x < w := lt_of_le_of_lt (le_max_left _ _) hwxs
      exact mem_rightAboveSet_of_lt_of_mem hwI hxw hwt htD
    have hfw_gt : f w > f x := by
      exact hwD.2.2 w ⟨hwD.2.1, le_rfl⟩
    have hfw_lt : f w < f (sSup D) := by
      have hw_left : sSup D - ε < w := by
        linarith [le_max_right x (sSup D - ε / 2), hwxs]
      exact hleft w hw_left hws
    have hfs_gt : f (sSup D) > f x := lt_trans hfw_gt hfw_lt
    let u : ℝ := sSup D + ε / 2
    have hsu : sSup D < u := by
      dsimp [u]
      linarith
    have huε : u < sSup D + ε := by
      dsimp [u]
      linarith
    have huI : u ∈ Set.Ioo a b := hεsub ⟨by dsimp [u]; linarith, huε⟩
    have huD : u ∈ D := by
      refine ⟨huI, lt_trans hx_lt_sSup hsu, ?_⟩
      intro z hz
      by_cases hzle : z ≤ sSup D
      · have hzx : x < z := hz.1
        rcases lt_or_eq_of_le hzle with hzslt | rfl
        · obtain ⟨t, htD, hzt⟩ : ∃ t ∈ D, z < t := by
            exact (lt_csSup_iff hDbdd hDnonempty).1 hzslt
          have hzI : z ∈ Set.Ioo a b := by
            refine ⟨?_, ?_⟩
            · exact lt_trans hx.1 hzx
            · exact lt_of_le_of_lt hz.2 huI.2
          have hzD : z ∈ D := mem_rightAboveSet_of_lt_of_mem hzI hzx hzt htD
          exact hzD.2.2 z ⟨hzx, le_rfl⟩
        · exact hfs_gt
      · have hzs : sSup D < z := lt_of_not_ge hzle
        have hfzs : f z > f (sSup D) := hright z hzs (lt_of_le_of_lt hz.2 huε)
        exact lt_trans hfs_gt hfzs
    exact (not_lt_of_ge (le_csSup hDbdd huD)) hsu
  have hy_lt_b : y < b := hy.2
  have hy_lt_sSup : y < sSup D := by
    rw [hsSup_eq_b]
    exact hy_lt_b
  obtain ⟨t, htD, hyt⟩ : ∃ t ∈ D, y < t := (lt_csSup_iff hDbdd hDnonempty).1 hy_lt_sSup
  have hyD : y ∈ D := mem_rightAboveSet_of_lt_of_mem hy hxy hyt htD
  exact hyD.2.2 y ⟨hxy, le_rfl⟩

/-- If `Φ+,−` holds at every point of an interval, then the function is strictly decreasing there. -/
theorem strictAntiOn_of_locPattern_pm {f : ℝ → ℝ} {a b : ℝ}
    (hpat : ∀ x ∈ Set.Ioo a b, locPattern_pm f a b x) :
    StrictAntiOn f (Set.Ioo a b) := by
  have hnegpat : ∀ x ∈ Set.Ioo a b, locPattern_mp (fun t => -f t) a b x := by
    intro x hx
    rcases hpat x hx with ⟨ε, hεpos, hεsub, hleft, hright⟩
    refine ⟨ε, hεpos, hεsub, ?_, ?_⟩
    · intro y hy1 hy2
      exact neg_lt_neg (hleft y hy1 hy2)
    · intro y hy1 hy2
      exact neg_lt_neg (hright y hy1 hy2)
  have hmono : StrictMonoOn (fun t => -f t) (Set.Ioo a b) :=
    strictMonoOn_of_locPattern_mp hnegpat
  intro x hx y hy hxy
  exact neg_lt_neg_iff.mp (hmono hx hy hxy)

end LeanOMIN
