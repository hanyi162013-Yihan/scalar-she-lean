module

public import SHEStochastic.MatrixProfileFixedPoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixProfileDisplacement
open MeasureTheory Set MatrixNonlinearCoefficient MatrixHeatCovariance MatrixProfileUpdate
open MatrixProfileFixedPoint SHE.ProfileVariance
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (G : Coefficient (Fin n))

/-- The actual fixed profile approaches its prescribed vector mean
with the expected r^(beta/4) Hölder displacement. -/
theorem bound (φ : Domain → EuclideanSpace ℝ (Fin n))
    (κ : Domain → Matrix (Fin n) (Fin n) ℝ) (hκ : Measurable κ)
    (hκS : ∀ p, κ p ∈ constraint G) {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (p : HeatCovarianceMeasure.Window × SpatialCircle)
    (hfix : κ (p.1.val,p.2) = update G φ κ p) :
    ‖κ (p.1.val,p.2)-G.covariance (φ (p.1.val,p.2))‖ ≤
      (2*(G.bound : ℝ)*K)*(upperConstant*upper G)^(β/2)*
        GaussianNormMoment.moment (Fin n) β*p.1.val^(β/4) := by
  have hLo (z : Domain) := (hκS z).1.1
  have hHi (z : Domain) := (hκS z).1.2
  have hM (z : Domain) := (hκS z).2
  have hp := MatrixHeatCovariance.positive κ hκ (upper G) G.lower (upper G)
    G.lower_pos hM hLo hHi p
  have hv : 0 ≤ upperConstant*upper G*p.1.val^(1/2 : ℝ) := by
    exact mul_nonneg (mul_nonneg upperConstant_pos.le (by unfold upper; positivity))
      (Real.rpow_nonneg p.1.property.1.le _)
  rw [hfix]
  have he := MatrixGaussianAverage.displacement G hK hβ hG (covariance κ p)
    hp.posSemidef.nonneg hv
    (small_bound κ (upper G) (by unfold upper; positivity) hM p) (φ (p.1.val,p.2))
  apply he.trans_eq
  rw [Real.mul_rpow (mul_nonneg upperConstant_pos.le (by unfold upper; positivity))
    (Real.rpow_nonneg p.1.property.1.le _),← Real.rpow_mul p.1.property.1.le,
    show (1/2 : ℝ)*(β/2)=β/4 by ring]
  ring

end SHEStochastic.MatrixProfileDisplacement
