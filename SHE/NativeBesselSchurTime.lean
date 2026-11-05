module
public import SHE.PolynomialGaussianTime
public import SHE.NativeBesselLaplace
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBesselSchurTime
open Set MeasureTheory Real

def clipped (ρ D t:ℝ):ℝ:=t^(ρ-1)*min 1 (D*t^(-(1/2:ℝ)))

theorem scale {D t:ℝ}(hD:0<D)(ht:0≤t):
    ((D^(-2:ℝ))*t)^(-(1/2:ℝ))=D*t^(-(1/2:ℝ)):=by
  rw [Real.mul_rpow (Real.rpow_nonneg hD.le _) ht,←Real.rpow_mul hD.le]
  norm_num

theorem integrable {ρ D:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(hD:0<D):
    IntegrableOn (clipped ρ D) (Ioi 0):=by
  apply (PolynomialGaussianTime.integrable hρ hρhalf (Real.rpow_pos_of_pos hD (-2))).congr_fun
    (fun t ht=>?_) measurableSet_Ioi
  simp only [PolynomialGaussianTime.kernel,clipped,scale hD ht.le]

theorem integral {ρ D:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(hD:0<D):
    (∫t in Ioi (0:ℝ),clipped ρ D t)=(1/ρ+1/(1/2-ρ))*D^(2*ρ):=by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht=>show clipped ρ D t=PolynomialGaussianTime.kernel ρ (1/2) (D^(-2:ℝ)) t by
      simp only [PolynomialGaussianTime.kernel,clipped,scale hD ht.le]),
    PolynomialGaussianTime.integral hρ hρhalf (Real.rpow_pos_of_pos hD (-2)),
    ←Real.rpow_mul hD.le]
  congr 2
  ring

/-- The clipped Schur marginal splits into the massive constant mode
and the sharp integrable spatial gain, without discarding the clip. -/
theorem min_split {B M t:ℝ}(hB:0≤B)(hM:0≤M)(ht:0≤t):
    min 1 ((1+B*t^(-(1/2:ℝ)))*M)≤M+min 1 (B*M*t^(-(1/2:ℝ))):=by
  have hq:0≤B*M*t^(-(1/2:ℝ)):=mul_nonneg (mul_nonneg hB hM) (Real.rpow_nonneg ht _)
  by_cases h:B*M*t^(-(1/2:ℝ))≤1
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans_eq (by ring)
  · rw [min_eq_left (le_of_not_ge h)]
    exact (min_le_left _ _).trans (by linarith)

end SHE.NativeBesselSchurTime
