import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic

open Set

namespace LeanOMIN

/-- Euclidean `n`-space over the reals, represented as `Fin n → ℝ`. -/
abbrev Rn (n : ℕ) := Fin n → ℝ

/-- Transport coordinates along an equivalence of finite index types. -/
def reindexRn {m n : ℕ} (e : Fin m ≃ Fin n) : Rn m ≃ Rn n where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by
    funext i
    simp
  right_inv y := by
    funext j
    simp

@[simp] theorem reindexRn_apply {m n : ℕ} (e : Fin m ≃ Fin n) (x : Rn m) (j : Fin n) :
    reindexRn e x j = x (e.symm j) := rfl

@[simp] theorem reindexRn_symm_apply {m n : ℕ} (e : Fin m ≃ Fin n) (y : Rn n) (i : Fin m) :
    (reindexRn e).symm y i = y (e i) := rfl

/-- The standard equivalence `ℝ^(m+n) ≃ ℝ^m × ℝ^n`. -/
def splitAtEquiv (m n : ℕ) : Rn (m + n) ≃ Rn m × Rn n :=
  (Equiv.piCongrLeft' (fun _ : Fin (m + n) => ℝ) (finSumFinEquiv.symm)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) ℝ)

@[simp] theorem splitAtEquiv_fin_append {m n : ℕ} (x : Rn m) (y : Rn n) :
    splitAtEquiv m n (Fin.append x y) = (x, y) := by
  ext i <;> simp [splitAtEquiv]

@[simp] theorem splitAtEquiv_symm_apply {m n : ℕ} (x : Rn m) (y : Rn n) :
    (splitAtEquiv m n).symm (x, y) = Fin.append x y := by
  apply (splitAtEquiv m n).injective
  simp

/-- View a real number as an element of `ℝ^1`. -/
def scalarToRn1 : ℝ → Rn 1 := fun x _ => x

/-- Extract the scalar coordinate from `ℝ^1`. -/
def rn1ToScalar : Rn 1 → ℝ := fun x => x 0

@[simp] theorem rn1ToScalar_scalarToRn1 (x : ℝ) : rn1ToScalar (scalarToRn1 x) = x := rfl

@[simp] theorem scalarToRn1_rn1ToScalar (x : Rn 1) : scalarToRn1 (rn1ToScalar x) = x := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  simp [scalarToRn1, rn1ToScalar, hi]

/-- `ℝ` and `ℝ^1` are equivalent. -/
def realEquivRn1 : ℝ ≃ Rn 1 where
  toFun := scalarToRn1
  invFun := rn1ToScalar
  left_inv := rn1ToScalar_scalarToRn1
  right_inv := scalarToRn1_rn1ToScalar

/-- Types that come with a chosen coordinatization by some `ℝ^n`. -/
class RnEncoding (α : Type*) where
  dim : ℕ
  equiv : α ≃ Rn dim

instance instRnEncodingRn (n : ℕ) : RnEncoding (Rn n) where
  dim := n
  equiv := Equiv.refl _

instance instRnEncodingReal : RnEncoding ℝ where
  dim := 1
  equiv := realEquivRn1

instance instRnEncodingProd (α β : Type*) [RnEncoding α] [RnEncoding β] : RnEncoding (α × β) where
  dim := RnEncoding.dim α + RnEncoding.dim β
  equiv :=
    (Equiv.prodCongr (RnEncoding.equiv (α := α)) (RnEncoding.equiv (α := β))).trans
      (splitAtEquiv (RnEncoding.dim α) (RnEncoding.dim β)).symm

/-- Encode a subset of a coordinatized type as a subset of the corresponding `ℝ^n`. -/
def encodeSet (α : Type*) [RnEncoding α] (A : Set α) : Set (Rn (RnEncoding.dim α)) :=
  (RnEncoding.equiv (α := α)).symm ⁻¹' A

/-- Transport a raw definable set along a coordinate reindexing. -/
def reindexSet {m n : ℕ} (e : Fin m ≃ Fin n) (A : Set (Rn m)) : Set (Rn n) :=
  (reindexRn e).symm ⁻¹' A

@[simp] theorem mem_reindexSet {m n : ℕ} {e : Fin m ≃ Fin n} {A : Set (Rn m)} {x : Rn n} :
    x ∈ reindexSet e A ↔ (reindexRn e).symm x ∈ A := Iff.rfl

@[simp] theorem mem_encodeSet_real {A : Set ℝ} {x : Rn 1} :
    x ∈ encodeSet ℝ A ↔ rn1ToScalar x ∈ A := by
  change realEquivRn1.symm x ∈ A ↔ rn1ToScalar x ∈ A
  rfl

@[simp] theorem mem_encodeSet_real_prod {A : Set (ℝ × ℝ)} {z : Rn 2} :
    z ∈ encodeSet (ℝ × ℝ) A ↔
      (rn1ToScalar (splitAtEquiv 1 1 z).1, rn1ToScalar (splitAtEquiv 1 1 z).2) ∈ A := by
  change
    (realEquivRn1.symm ((splitAtEquiv 1 1 z).1), realEquivRn1.symm ((splitAtEquiv 1 1 z).2)) ∈ A
      ↔
        (rn1ToScalar ((splitAtEquiv 1 1 z).1), rn1ToScalar ((splitAtEquiv 1 1 z).2)) ∈ A
  rfl

/-- The graph of a function over a domain. -/
def rawGraph {α β : Type*} (A : Set α) (f : α → β) : Set (α × β) :=
  {p | p.1 ∈ A ∧ p.2 = f p.1}

/-- Definability for arbitrary coordinatized sets, relative to a raw definability predicate on `ℝ^n`. -/
def DefinableSetOf
    (Def : ∀ {n : ℕ}, Set (Rn n) → Prop) {α : Type*} [RnEncoding α] (A : Set α) : Prop :=
  Def (encodeSet α A)

/-- Definability for maps between coordinatized sets, via graph definability. -/
def DefinableMapOf
    (Def : ∀ {n : ℕ}, Set (Rn n) → Prop) {α β : Type*} [RnEncoding α] [RnEncoding β]
    (A : Set α) (f : α → β) : Prop :=
  DefinableSetOf Def (rawGraph A f)

/-- Definability for scalar-valued maps, used frequently for cell sections. -/
def DefinableScalarMapOf
    (Def : ∀ {n : ℕ}, Set (Rn n) → Prop) {α : Type*} [RnEncoding α]
    (A : Set α) (f : α → ℝ) : Prop :=
  DefinableMapOf Def A f

/-- The raw projection along the last `n` coordinates. -/
def prefixProjection (m n : ℕ) (A : Set (Rn (m + n))) : Set (Rn m) :=
  {x | ∃ y, Fin.append x y ∈ A}

@[simp] theorem mem_prefixProjection {m n : ℕ} {A : Set (Rn (m + n))} {x : Rn m} :
    x ∈ prefixProjection m n A ↔ ∃ y, Fin.append x y ∈ A := Iff.rfl

/-- The product of two raw definable subsets, transported into `ℝ^(m+n)`. -/
def rawProdSet (m n : ℕ) (A : Set (Rn m)) (B : Set (Rn n)) : Set (Rn (m + n)) :=
  {z | (splitAtEquiv m n z).1 ∈ A ∧ (splitAtEquiv m n z).2 ∈ B}

@[simp] theorem mem_rawProdSet {m n : ℕ} {A : Set (Rn m)} {B : Set (Rn n)} {z : Rn (m + n)} :
    z ∈ rawProdSet m n A B ↔
      (splitAtEquiv m n z).1 ∈ A ∧ (splitAtEquiv m n z).2 ∈ B := Iff.rfl

end LeanOMIN
