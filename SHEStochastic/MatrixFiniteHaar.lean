module

public import SHEStochastic.MatrixHaarAlgebra
public import SHE.SignedTransport
import all Mathlib.Analysis.RCLike.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixFiniteHaar
open Matrix Finset SHE.FiniteHaar
open MatrixHaarAlgebra
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Use the existing scalar binary grids and detail indices unchanged. -/
def totalMass (n : ℕ) (κ : Grid n → Matrix d d ℝ) : Matrix d d ℝ := ∑ x, κ x

theorem totalMass_posDef (n : ℕ) (κ : Grid n → Matrix d d ℝ) (hκ : ∀ x, (κ x).PosDef) :
    (totalMass n κ).PosDef := Matrix.posDef_sum univ_nonempty (fun x _ ↦ hκ x)

def detailColumn : (n : ℕ) → (Grid n → Matrix d d ℝ) → DetailIndex n → Grid n → Matrix d d ℝ
  | 0, _, k => nomatch k
  | n+1, κ, Sum.inl _ => Sum.elim
    (fun _ ↦ left (totalMass n (fun x ↦ κ (Sum.inl x))) (totalMass n (fun x ↦ κ (Sum.inr x))))
    (fun _ ↦ right (totalMass n (fun x ↦ κ (Sum.inl x))) (totalMass n (fun x ↦ κ (Sum.inr x))))
  | n+1, κ, Sum.inr (Sum.inl k) => Sum.elim (detailColumn n (fun x ↦ κ (Sum.inl x)) k) (fun _ ↦ 0)
  | n+1, κ, Sum.inr (Sum.inr k) => Sum.elim (fun _ ↦ 0) (detailColumn n (fun x ↦ κ (Sum.inr x)) k)

def weightedMean {α : Type*} [Fintype α] (κ u : α → Matrix d d ℝ) : Matrix d d ℝ := ∑ x, κ x*u x

def weightedGram {α : Type*} [Fintype α] (κ u v : α → Matrix d d ℝ) : Matrix d d ℝ :=
  ∑ x, (u x)ᴴ*κ x*v x

theorem mean_const {α : Type*} [Fintype α] (κ : α → Matrix d d ℝ) (A : Matrix d d ℝ) :
    weightedMean κ (fun _ ↦ A) = (∑ x, κ x)*A := (Finset.sum_mul _ _ _).symm

theorem mean_zero {α : Type*} [Fintype α] (κ : α → Matrix d d ℝ) : weightedMean κ (fun _ ↦ 0) = 0 := by
  simp only [weightedMean, mul_zero, Finset.sum_const_zero]

theorem gram_const_const {α : Type*} [Fintype α] (κ : α → Matrix d d ℝ) (A B : Matrix d d ℝ) :
    weightedGram κ (fun _ ↦ A) (fun _ ↦ B) = Aᴴ*(∑ x, κ x)*B := by
  rw [weightedGram, Finset.mul_sum, Finset.sum_mul]

theorem gram_const_left {α : Type*} [Fintype α] (κ v : α → Matrix d d ℝ) (A : Matrix d d ℝ) :
    weightedGram κ (fun _ ↦ A) v = Aᴴ*weightedMean κ v := by
  simp only [weightedGram, weightedMean, Finset.mul_sum, mul_assoc]

theorem gram_const_right {α : Type*} [Fintype α] (κ u : α → Matrix d d ℝ)
    (hκ : ∀ x, (κ x).IsHermitian) (B : Matrix d d ℝ) :
    weightedGram κ u (fun _ ↦ B) = (weightedMean κ u)ᴴ*B := by
  simp only [weightedGram, weightedMean, Matrix.conjTranspose_sum, Finset.sum_mul,
    conjTranspose_mul, fun x ↦ (hκ x).eq]

theorem gram_zero_left {α : Type*} [Fintype α] (κ v : α → Matrix d d ℝ) :
    weightedGram κ (fun _ ↦ 0) v = 0 := by
  simp only [weightedGram, conjTranspose_zero, zero_mul, Finset.sum_const_zero]

theorem gram_zero_right {α : Type*} [Fintype α] (κ u : α → Matrix d d ℝ) :
    weightedGram κ u (fun _ ↦ 0) = 0 := by
  simp only [weightedGram, mul_zero, Finset.sum_const_zero]

theorem mean_sum {α β : Type*} [Fintype α] [Fintype β]
    (κ : Sum α β → Matrix d d ℝ) (u : α → Matrix d d ℝ) (v : β → Matrix d d ℝ) :
    weightedMean κ (Sum.elim u v) = weightedMean (fun x ↦ κ (Sum.inl x)) u+
      weightedMean (fun x ↦ κ (Sum.inr x)) v := by
  simp only [weightedMean, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem gram_sum {α β : Type*} [Fintype α] [Fintype β]
    (κ : Sum α β → Matrix d d ℝ) (u₁ v₁ : α → Matrix d d ℝ) (u₂ v₂ : β → Matrix d d ℝ) :
    weightedGram κ (Sum.elim u₁ u₂) (Sum.elim v₁ v₂) =
      weightedGram (fun x ↦ κ (Sum.inl x)) u₁ v₁+weightedGram (fun x ↦ κ (Sum.inr x)) u₂ v₂ := by
  simp only [weightedGram, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Cancellation at every node of the original finite Haar tree. -/
theorem cancellation (n : ℕ) (κ : Grid n → Matrix d d ℝ) (hκ : ∀ x, (κ x).PosDef)
    (k : DetailIndex n) : weightedMean κ (detailColumn n κ k) = 0 := by
  induction n with
  | zero => exact Empty.elim k
  | succ n ih =>
    dsimp only [Grid, DetailIndex, gridFintype, detailFintype] at κ hκ k ⊢
    rcases k with k | (k | k)
    · simp only [detailColumn]
      erw [mean_sum]
      rw [mean_const, mean_const]
      exact MatrixHaarAlgebra.weighted_mean _ _
        (totalMass_posDef n _ (fun x ↦ hκ (Sum.inl x)))
        (totalMass_posDef n _ (fun x ↦ hκ (Sum.inr x)))
    · simp only [detailColumn]
      erw [mean_sum]
      rw [mean_zero, add_zero]
      exact ih _ (fun x ↦ hκ (Sum.inl x)) k
    · simp only [detailColumn]
      erw [mean_sum]
      rw [mean_zero, zero_add]
      exact ih _ (fun x ↦ hκ (Sum.inr x)) k

/-- All detail blocks of the finite tree are mutually orthonormal,
including nested branches and every off-diagonal component pairing. -/
theorem detail_gram (n : ℕ) (κ : Grid n → Matrix d d ℝ) (hκ : ∀ x, (κ x).PosDef)
    (k j : DetailIndex n) :
    weightedGram κ (detailColumn n κ k) (detailColumn n κ j) = if k=j then 1 else 0 := by
  induction n with
  | zero => exact Empty.elim k
  | succ n ih =>
    dsimp only [Grid, DetailIndex, gridFintype, detailFintype] at κ hκ k j ⊢
    have hcl : ∀ x, (κ (Sum.inl x)).PosDef := fun x ↦ hκ (Sum.inl x)
    have hcr : ∀ x, (κ (Sum.inr x)).PosDef := fun x ↦ hκ (Sum.inr x)
    rcases k with ⟨⟩ | (k | k) <;> rcases j with ⟨⟩ | (j | j)
    all_goals simp only [detailColumn]
    all_goals erw [gram_sum]
    all_goals simp only [gram_zero_left, gram_zero_right, add_zero, zero_add,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]
    · rw [gram_const_const, gram_const_const]
      exact MatrixHaarAlgebra.weighted_gram _ _ (totalMass_posDef n _ hcl) (totalMass_posDef n _ hcr)
    · rw [gram_const_left, cancellation n _ hcl, mul_zero]
    · rw [gram_const_left, cancellation n _ hcr, mul_zero]
    · rw [gram_const_right _ _ (fun x ↦ (hcl x).isHermitian) _, cancellation n _ hcl,
        conjTranspose_zero, zero_mul]
    · exact ih _ hcl k j
    · rw [gram_const_right _ _ (fun x ↦ (hcr x).isHermitian) _, cancellation n _ hcr,
        conjTranspose_zero, zero_mul]
    · exact ih _ hcr k j

def inverseSqrt (A : Matrix d d ℝ) : Matrix d d ℝ := (CFC.sqrt A)⁻¹

theorem inverseSqrt_gram (A : Matrix d d ℝ) (hA : A.PosDef) :
    (inverseSqrt A)ᴴ*A*inverseSqrt A = 1 := by
  have hs : 0≤A := hA.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt A) := (CFC.isUnit_sqrt_iff A hs).mpr hA.isUnit
  letI : Invertible (CFC.sqrt A) := hu.invertible
  have hh : (inverseSqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian.inv
  rw [hh.eq]
  change (CFC.sqrt A)⁻¹*A*(CFC.sqrt A)⁻¹=1
  calc
    _ = (CFC.sqrt A)⁻¹*(CFC.sqrt A*CFC.sqrt A)*(CFC.sqrt A)⁻¹ :=
      congrArg (fun B ↦ (CFC.sqrt A)⁻¹*B*(CFC.sqrt A)⁻¹) (CFC.sqrt_mul_sqrt_self A hs).symm
    _ = 1 := by simp only [← mul_assoc, Matrix.inv_mul_of_invertible, one_mul, Matrix.mul_inv_of_invertible]

def haarColumn (n : ℕ) (κ : Grid n → Matrix d d ℝ) : Option (DetailIndex n) → Grid n → Matrix d d ℝ
  | none => fun _ ↦ inverseSqrt (totalMass n κ)
  | some k => detailColumn n κ k

/-- The root and every detail block form the matrix weighted Haar frame
on the original scalar binary grid. -/
theorem haar_gram (n : ℕ) (κ : Grid n → Matrix d d ℝ) (hκ : ∀ x, (κ x).PosDef)
    (k j : Option (DetailIndex n)) :
    weightedGram κ (haarColumn n κ k) (haarColumn n κ j) = if k=j then 1 else 0 := by
  cases k with
  | none =>
    cases j with
    | none =>
      simp only [haarColumn, ite_true, gram_const_const]
      exact inverseSqrt_gram _ (totalMass_posDef n κ hκ)
    | some j =>
      simp only [haarColumn, reduceCtorEq, ite_false, gram_const_left, cancellation n κ hκ j, mul_zero]
  | some k =>
    cases j with
    | none =>
      simp only [haarColumn, reduceCtorEq, ite_false,
        gram_const_right κ _ (fun x ↦ (hκ x).isHermitian) _, cancellation n κ hκ k, conjTranspose_zero, zero_mul]
    | some j =>
      simpa only [haarColumn, Option.some.injEq] using detail_gram n κ hκ k j

end SHEStochastic.MatrixFiniteHaar
