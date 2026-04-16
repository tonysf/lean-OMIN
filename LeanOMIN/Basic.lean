import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic

open Set

namespace LeanOMIN

/-- Euclidean `n`-space over the reals, represented as `Fin n → ℝ`. -/
abbrev Rn (n : ℕ) := Fin n → ℝ

/-- The standard equivalence `ℝ^(m+n) ≃ ℝ^m × ℝ^n`. -/
def splitAtEquiv (m n : ℕ) : Rn (m + n) ≃ Rn m × Rn n :=
  (Equiv.piCongrLeft' (fun _ : Fin (m + n) => ℝ) (finSumFinEquiv.symm)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) ℝ)

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
