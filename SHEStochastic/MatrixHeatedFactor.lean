module

public import SHEStochastic.VectorWhiteHeatTrace
public import SHEStochastic.MatrixHaarOperatorBounds
public import SHEStochastic.MatrixPredictableHaarRotation
public import SHE.HilbertTrace
public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixHeatedFactor
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem input_basis (k : d × HaarNode) : MatrixPredictableHaarRotation.basis k = lp.single 2 k 1 :=
  (HilbertBasis.repr_symm_single (MatrixPredictableHaarRotation.basis (d := d)) k).symm

/-- The actual infinite covariance-adapted factor becomes
Hilbert--Schmidt after every positive heat time. This reuses the
ordinary vector heat trace and the right-composition ideal estimate. -/
theorem energy {t : ℝ} (ht : 0 < t) (P : Profile d) :
    Summable (fun k : d × HaarNode => ‖VectorHeat.heat t (factor P (lp.single 2 k 1))‖ ^ 2) ∧
      (∑' k : d × HaarNode, ‖VectorHeat.heat t (factor P (lp.single 2 k 1))‖ ^ 2) ≤
        (Fintype.card d : ℝ) * P.upper *
          (1 + 2 * HeatTrace.fractionalGaussianIntegral 0 * t ^ (-(1/2 : ℝ))) := by
  have hheat := VectorWhiteHeatTrace.trace (d := d) ht
  have hh := HilbertTrace.right_comp (VectorHeat.heat t) (factor P)
    VectorWhiteCoordinates.basis VectorWhiteCoordinates.basis MatrixPredictableHaarRotation.basis hheat.1
  simp only [ContinuousLinearMap.comp_apply, input_basis] at hh
  have hNorm : ‖factor P‖ ^ 2 ≤ P.upper :=
    (pow_le_pow_left₀ (norm_nonneg _) (MatrixHaarOperatorBounds.factor_norm P) 2).trans_eq
      (Real.sq_sqrt P.upper_pos.le)
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact (mul_le_mul hNorm hheat.2 (tsum_nonneg (fun _ => sq_nonneg _)) P.upper_pos.le).trans_eq (by ring)

def columns {t : ℝ} (ht : 0 < t) (P : Profile d) :
    HilbertColumns.Space (d × HaarNode) (Physical (d := d)) :=
  HilbertColumns.ofSummable (fun k => VectorHeat.heat t (factor P (lp.single 2 k 1))) (energy ht P).1

theorem columns_bound {t : ℝ} (ht : 0 < t) (P : Profile d) :
    ‖columns ht P‖ ^ 2 ≤ (Fintype.card d : ℝ) * P.upper *
      (1 + 2 * HeatTrace.fractionalGaussianIntegral 0 * t ^ (-(1/2 : ℝ))) := by
  rw [HilbertColumns.norm_sq]
  exact (energy ht P).2

end SHEStochastic.MatrixHeatedFactor
