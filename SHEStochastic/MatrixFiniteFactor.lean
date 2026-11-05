module

public import SHEStochastic.MatrixFiniteHaar
public import Mathlib.Data.Matrix.Block

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixFiniteFactor
open Matrix Finset SHE.FiniteHaar MatrixFiniteHaar

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Flatten only the finite state components; keep the existing leaf
and Haar-mode types for the spatial tree. -/
def haarMatrix (n : ℕ) (κ : Grid n → Matrix d d ℝ) :
    Matrix (d × Grid n) (d × Option (DetailIndex n)) ℝ :=
  fun x k ↦ MatrixFiniteHaar.haarColumn n κ k.2 x.2 x.1 k.1

def localFactor (n : ℕ) (κ : Grid n → Matrix d d ℝ) :
    Matrix (d × Grid n) (d × Option (DetailIndex n)) ℝ :=
  fun x k ↦ (κ x.2*MatrixFiniteHaar.haarColumn n κ k.2 x.2) x.1 k.1

theorem gram_entry {α : Type*} [Fintype α] (κ u v : α → Matrix d d ℝ) (i j : d) :
    weightedGram κ u v i j = ∑ x : α, ∑ r : d, ∑ q : d, u x r i*(κ x r q*v x q j) := by
  simp only [weightedGram, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- Weighted orthogonality gives an exact left inverse of the actual
matrix-valued factor, with all state-component cross terms retained. -/
theorem left_inverse (n : ℕ) (κ : Grid n → Matrix d d ℝ) (hκ : ∀ x, (κ x).PosDef) :
    (haarMatrix n κ)ᴴ*localFactor n κ=1 := by
  ext ⟨i,k⟩ ⟨j,l⟩
  have hh := congrArg (fun A : Matrix d d ℝ ↦ A i j) (haar_gram n κ hκ k l)
  rw [gram_entry] at hh
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, haarMatrix, localFactor,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  convert hh using 1
  · by_cases hkl : k=l <;> by_cases hij : i=j <;> simp [hkl,hij,Matrix.one_apply,Prod.mk.injEq]

/-- Cardinality and the proved left inverse give completeness of the
finite matrix Haar frame; no basis property is assumed. -/
theorem right_inverse (n : ℕ) (κ : Grid n → Matrix d d ℝ) (hκ : ∀ x, (κ x).PosDef) :
    localFactor n κ*(haarMatrix n κ)ᴴ=1 := by
  apply (Matrix.mul_eq_one_comm_of_card_eq _ _ ℝ (by
    simp only [Fintype.card_prod, card_modes])).mp
  exact left_inverse n κ hκ

/-- The factor columns are the ordered matrix products κχ. -/
theorem factor_eq (n : ℕ) (κ : Grid n → Matrix d d ℝ) :
    localFactor n κ=Matrix.blockDiagonal κ*haarMatrix n κ := by
  ext ⟨i,x⟩ ⟨j,k⟩
  simp [localFactor, haarMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]

/-- Exact finite-grid covariance LL*=Mκ, obtained from the same
Haar columns used in the manuscript's matrix construction. -/
theorem covariance (n : ℕ) (κ : Grid n → Matrix d d ℝ) (hκ : ∀ x, (κ x).PosDef) :
    localFactor n κ*(localFactor n κ)ᴴ=Matrix.blockDiagonal κ := by
  have hHerm : (Matrix.blockDiagonal κ)ᴴ=Matrix.blockDiagonal κ := by
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext x
    exact (hκ x).isHermitian.eq
  calc
    _ = (localFactor n κ*(haarMatrix n κ)ᴴ)*(Matrix.blockDiagonal κ)ᴴ := by
      conv_lhs => rhs; rw [factor_eq]
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [right_inverse n κ hκ, Matrix.one_mul, hHerm]

end SHEStochastic.MatrixFiniteFactor
