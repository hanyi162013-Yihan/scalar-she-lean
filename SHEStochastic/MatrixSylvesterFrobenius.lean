module

public import SHE.SignedTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixSylvesterFrobenius
open Matrix Finset SHE.FiniteTransport

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def pairing (A B : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, A i j*B i j

theorem pairing_transpose (A B : Matrix ι κ ℝ) : pairing Aᵀ Bᵀ=pairing A B := by
  simp only [pairing, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem pairing_add (A B C : Matrix ι κ ℝ) : pairing A (B+C)=pairing A B+pairing A C := by
  simp only [pairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairing_sq_le (A B : Matrix ι κ ℝ) :
    pairing A B^2≤frobeniusSq A*frobeniusSq B := by
  simpa only [pairing, frobeniusSq, Fintype.sum_prod_type, Finset.mem_univ, forall_const, sum_attach] using
    sum_mul_sq_le_sq_mul_sq (univ : Finset (ι×κ)) (fun p ↦ A p.1 p.2) (fun p ↦ B p.1 p.2)

/-- A quadratic lower bound applies to every column without a dimension loss. -/
theorem left_lower (A : Matrix ι ι ℝ) (D : Matrix ι κ ℝ) (a : ℝ)
    (hA : ∀ x : ι → ℝ, a*vectorSq x≤x ⬝ᵥ (A*ᵥx)) :
    a*frobeniusSq D≤pairing D (A*D) := by
  calc
    _ = ∑ j : κ, a*vectorSq (fun i ↦ D i j) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ ≤ ∑ j : κ, (fun i ↦ D i j) ⬝ᵥ (A*ᵥ(fun i ↦ D i j)) := Finset.sum_le_sum (fun j _ ↦ hA _)
    _ = _ := by
      simp only [pairing, dotProduct, Matrix.mulVec, Matrix.mul_apply]
      exact Finset.sum_comm

/-- The corresponding row estimate uses the transpose quadratic form. -/
theorem right_lower (B : Matrix κ κ ℝ) (D : Matrix ι κ ℝ) (b : ℝ)
    (hB : ∀ x : κ → ℝ, b*vectorSq x≤x ⬝ᵥ (Bᵀ*ᵥx)) :
    b*frobeniusSq D≤pairing D (D*B) := by
  have hh := left_lower Bᵀ Dᵀ b hB
  simpa only [← Matrix.transpose_mul, frobeniusSq_transpose, pairing_transpose] using hh

/-- Quantitative injectivity of the two-sided Sylvester operator in
Frobenius norm. Only finite quadratic lower bounds and Cauchy--Schwarz
are used; no matrix square-root differentiability theorem is assumed. -/
theorem lower (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (D : Matrix ι κ ℝ)
    (a b : ℝ) (hab : 0≤a+b)
    (hA : ∀ x : ι → ℝ, a*vectorSq x≤x ⬝ᵥ (A*ᵥx))
    (hB : ∀ x : κ → ℝ, b*vectorSq x≤x ⬝ᵥ (Bᵀ*ᵥx)) :
    (a+b)^2*frobeniusSq D≤frobeniusSq (A*D+D*B) := by
  let S := A*D+D*B
  have hLow : (a+b)*frobeniusSq D≤pairing D S := by
    have h1 := left_lower A D a hA
    have h2 := right_lower B D b hB
    rw [show pairing D S=pairing D (A*D)+pairing D (D*B) from pairing_add _ _ _]
    nlinarith
  have h0 := frobeniusSq_nonneg D
  have hSquare : ((a+b)*frobeniusSq D)^2≤pairing D S^2 :=
    (sq_le_sq₀ (mul_nonneg hab h0) ((mul_nonneg hab h0).trans hLow)).mpr hLow
  have hCS := pairing_sq_le D S
  by_cases hD : frobeniusSq D=0
  · rw [hD, mul_zero]
    exact frobeniusSq_nonneg S
  have hPos : 0<frobeniusSq D := lt_of_le_of_ne h0 (Ne.symm hD)
  apply (mul_le_mul_iff_left₀ hPos).mp
  nlinarith only [hSquare, hCS]

/-- A direct signed square-root comparison, valid for noncommuting
positive symmetric matrices and with no interpolation argument. -/
theorem difference_sq (A B : Matrix ι ι ℝ) (a b : ℝ) (hab : 0≤a+b)
    (hA : ∀ x : ι → ℝ, a*vectorSq x≤x ⬝ᵥ (A*ᵥx))
    (hB : ∀ x : ι → ℝ, b*vectorSq x≤x ⬝ᵥ (Bᵀ*ᵥx)) :
    (a+b)^2*frobeniusSq (A-B)≤frobeniusSq (A*A-B*B) := by
  have hh := lower A B (A-B) a b hab hA hB
  have he : A*(A-B)+(A-B)*B=A*A-B*B := by noncomm_ring
  rwa [he] at hh

end SHEStochastic.MatrixSylvesterFrobenius
