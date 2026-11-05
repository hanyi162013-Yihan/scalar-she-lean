module

public import SHEStochastic.MatrixGaussianAverage
public import SHEStochastic.MatrixHeatCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixProfileUpdate
open MeasureTheory Set MatrixNonlinearCoefficient MatrixHeatCovariance
open SHE.ProfileVariance SHE.GaussianAudit SHE.GaussianSignedCovariance
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def update (G : Coefficient (Fin n)) (φ : Domain → EuclideanSpace ℝ (Fin n))
    (κ : Domain → Matrix (Fin n) (Fin n) ℝ) (p : HeatCovarianceMeasure.Window × SpatialCircle) :
    Matrix (Fin n) (Fin n) ℝ :=
  MatrixGaussianAverage.average G (covariance κ p) (φ (p.1.val,p.2))

theorem measurable (G : Coefficient (Fin n)) (φ : Domain → EuclideanSpace ℝ (Fin n))
    (hφ : Measurable φ) (κ : Domain → Matrix (Fin n) (Fin n) ℝ)
    (hκ : Measurable κ) (M : ℝ) (hM : ∀ p, ‖κ p‖ ≤ M) :
    Measurable (update G φ κ) := by
  have hp : Measurable (fun p : HeatCovarianceMeasure.Window × SpatialCircle =>
      (p.1.val,p.2)) := (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hm := (MatrixGaussianAverage.measurable G).comp
    ((MatrixHeatCovariance.measurable κ hκ M hM).prodMk (hφ.comp hp))
  exact hm

theorem norm_bound (G : Coefficient (Fin n)) (φ : Domain → EuclideanSpace ℝ (Fin n))
    (κ : Domain → Matrix (Fin n) (Fin n) ℝ) (p : HeatCovarianceMeasure.Window × SpatialCircle) :
    ‖update G φ κ p‖ ≤ (G.bound : ℝ)^2 := MatrixGaussianAverage.norm_bound G _ _

theorem elliptic (G : Coefficient (Fin n)) (φ : Domain → EuclideanSpace ℝ (Fin n))
    (κ : Domain → Matrix (Fin n) (Fin n) ℝ) (p : HeatCovarianceMeasure.Window × SpatialCircle) :
    G.lower • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ update G φ κ p ∧
      update G φ κ p ≤ ((G.bound : ℝ)^2+1) • (1 : Matrix (Fin n) (Fin n) ℝ) :=
  MatrixGaussianAverage.elliptic G _ _

def contractionConstant (G : Coefficient (Fin n)) (K β : ℝ) : ℝ :=
  upperConstant*((2*(G.bound : ℝ)*K)*secondScoreAbsIncrementMoment β)*
    (lowerConstant*G.lower)^(β/2-1)*covarianceBoundConstant n

theorem contractionConstant_nonneg (G : Coefficient (Fin n)) {K β : ℝ} (hK : 0 ≤ K) :
    0 ≤ contractionConstant G K β := by
  unfold contractionConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg upperConstant_pos.le
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK)
      (SHE.GaussianProfile.incrementMoment_nonneg β)))
    (Real.rpow_nonneg (mul_nonneg lowerConstant_pos.le G.lower_pos.le) _))
    (covarianceBoundConstant_nonneg n)

/-- The full coupled matrix update contracts with the same positive
small-time power as the scalar profile. Covariance differences need not
have a sign, and cross-component entries are retained. -/
theorem contraction (G : Coefficient (Fin n)) {K β D M : ℝ}
    (hK : 0 ≤ K) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (φ : Domain → EuclideanSpace ℝ (Fin n))
    (κ η : Domain → Matrix (Fin n) (Fin n) ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (hκM : ∀ z, ‖κ z‖ ≤ M) (hηM : ∀ z, ‖η z‖ ≤ M)
    (hκLo : ∀ z, G.lower • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ κ z)
    (hηLo : ∀ z, G.lower • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ η z)
    (hκHi : ∀ z, κ z ≤ M • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hηHi : ∀ z, η z ≤ M • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hDiff : ∀ z, ‖κ z-η z‖ ≤ D) (p : HeatCovarianceMeasure.Window × SpatialCircle) :
    ‖update G φ κ p-update G φ η p‖ ≤ contractionConstant G K β*p.1.val^(β/4)*D := by
  have hr := p.1.property.1
  have hlo : 0 < lowerConstant*G.lower*p.1.val^(1/2 : ℝ) :=
    mul_pos (mul_pos lowerConstant_pos G.lower_pos) (Real.rpow_pos_of_pos hr _)
  have hκl := lower_bound κ hκ M G.lower M G.lower_pos.le hκM hκLo hκHi p
  have hηl := lower_bound η hη M G.lower M G.lower_pos.le hηM hηLo hηHi p
  have hg := MatrixGaussianAverage.covariance_lipschitz G hlo hK hβ hG
    (covariance κ p) (covariance η p) hκl hηl (φ (p.1.val,p.2))
  have hc : 0 ≤ ((2*(G.bound : ℝ)*K)*secondScoreAbsIncrementMoment β*
      (lowerConstant*G.lower*p.1.val^(1/2 : ℝ))^(β/2-1))*covarianceBoundConstant n :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK)
      (SHE.GaussianProfile.incrementMoment_nonneg β)) (Real.rpow_nonneg hlo.le _))
      (covarianceBoundConstant_nonneg n)
  have hb := hg.trans (mul_le_mul_of_nonneg_left
    (difference κ η hκ hη M D hD hκM hηM hDiff p) hc)
  apply hb.trans_eq
  rw [Real.mul_rpow (mul_nonneg lowerConstant_pos.le G.lower_pos.le) (Real.rpow_nonneg hr.le _)]
  calc
    _ = contractionConstant G K β*D*
        ((p.1.val^(1/2 : ℝ))^(β/2-1)*p.1.val^(1/2 : ℝ)) := by
      unfold contractionConstant
      ring
    _ = _ := by
      rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr,
        show (1/2 : ℝ)*(β/2-1)+1/2=β/4 by ring]
      ring

end SHEStochastic.MatrixProfileUpdate
