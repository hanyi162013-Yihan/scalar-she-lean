module

public import SHEStochastic.MatrixGaussianMollifier
public import SHEStochastic.MatrixPositiveSqrtLipschitz

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixSmoothCoefficient
open MeasureTheory SHE MatrixNonlinearCoefficient MatrixGaussianMollifier
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff
variable {n : ℕ} (G : Coefficient (Fin n))

theorem sqrt_norm_bound (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖CFC.sqrt (covariance G ε z)‖ ≤ G.bound := by
  apply (sq_le_sq₀ (norm_nonneg _) G.bound.coe_nonneg).mp
  rw [MatrixSqrtReference.sqrt_norm_sq _ (nonnegative G ε z)]
  exact norm_bound G ε z

/-- Smooth positive diffusion approximants retain the original uniform
diffusion bound and lower covariance bound. -/
def coefficient (ε : ℝ) : Coefficient (Fin n) where
  value z := CFC.sqrt (covariance G ε z)
  measurable := CFC.measurable_sqrt.comp (MatrixGaussianMollifier.measurable G ε)
  bound := G.bound
  norm_bound := sqrt_norm_bound G ε
  lower := G.lower
  lower_pos := G.lower_pos
  lower_bound z := by
    rw [← Matrix.star_eq_conjTranspose,(CFC.sqrt_nonneg (covariance G ε z)).star_eq,
      CFC.sqrt_mul_sqrt_self _ (nonnegative G ε z)]
    exact (elliptic G ε z).1

theorem covariance_eq (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    (coefficient G ε).covariance z=covariance G ε z := by
  change CFC.sqrt (covariance G ε z)*star (CFC.sqrt (covariance G ε z))=_
  rw [(CFC.sqrt_nonneg (covariance G ε z)).star_eq,CFC.sqrt_mul_sqrt_self _ (nonnegative G ε z)]

theorem smooth {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (coefficient G ε).value := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact MatrixSqrtSmooth.comp (MatrixGaussianMollifier.smooth G hε).contDiffAt
    (positive G ε z) (Filter.Eventually.of_forall fun w => nonnegative G ε w)

def sqrtConstant : ℝ := MatrixPositiveSqrtLipschitz.constant (Fin n) (Real.sqrt G.lower)

theorem sqrtConstant_nonneg : 0 ≤ sqrtConstant G :=
  MatrixPositiveSqrtLipschitz.constant_nonneg (Real.sqrt_nonneg _)

theorem difference (ε : ℝ) (z w : EuclideanSpace ℝ (Fin n)) :
    ‖(coefficient G ε).value z-(coefficient G ε).value w‖ ≤
      sqrtConstant G*‖covariance G ε z-covariance G ε w‖ := by
  apply MatrixPositiveSqrtLipschitz.bound _ _ (Real.sqrt_pos.mpr G.lower_pos)
  · rw [Real.sq_sqrt G.lower_pos.le]
    exact (elliptic G ε z).1
  · rw [Real.sq_sqrt G.lower_pos.le]
    exact (elliptic G ε w).1

theorem holder {K β : ℝ} (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (ε : ℝ) (z w : EuclideanSpace ℝ (Fin n)) :
    ‖(coefficient G ε).value z-(coefficient G ε).value w‖ ≤
      (sqrtConstant G*(2*(G.bound : ℝ)*K))*‖z-w‖^β :=
  (difference G ε z w).trans ((mul_le_mul_of_nonneg_left
    (MatrixGaussianMollifier.holder G hG ε z w) (sqrtConstant_nonneg G)).trans_eq (by ring))

theorem lipschitz {ε K β : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) (z w : EuclideanSpace ℝ (Fin n)) :
    ‖(coefficient G ε).value z-(coefficient G ε).value w‖ ≤
      (sqrtConstant G*((2*(G.bound : ℝ)*K)*GaussianNormMoment.moment (Fin n) (β+1)*
        ε^((β-1)/2)))*‖z-w‖ :=
  (difference G ε z w).trans ((mul_le_mul_of_nonneg_left
    (MatrixGaussianMollifier.lipschitz G hε hK hβ hG z w) (sqrtConstant_nonneg G)).trans_eq (by ring))

/-- Uniform approximation is to the canonical positive square root of
GG*, which has already been linked to the original G by native rotation. -/
theorem error {ε K β : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) (z : EuclideanSpace ℝ (Fin n)) :
    ‖(coefficient G ε).value z-CFC.sqrt (G.covariance z)‖ ≤
      sqrtConstant G*((2*(G.bound : ℝ)*K)*ε^(β/2)*GaussianNormMoment.moment (Fin n) β) := by
  have he := MatrixPositiveSqrtLipschitz.bound (covariance G ε z) (G.covariance z)
    (Real.sqrt_pos.mpr G.lower_pos)
    (by rw [Real.sq_sqrt G.lower_pos.le]; exact (elliptic G ε z).1)
    (by rw [Real.sq_sqrt G.lower_pos.le]; exact G.lower_bound z)
  exact he.trans (mul_le_mul_of_nonneg_left (MatrixGaussianMollifier.error G hε hK hβ hG z)
    (sqrtConstant_nonneg G))

end SHEStochastic.MatrixSmoothCoefficient
