module
public import SHE.NativeBesselLaplace
public import SHE.NativeFourierSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBesselHeatEnergy
open Set MeasureTheory Real AddCircle StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

def heatMass (t:ℝ)(f:CircleL2):ℝ≥0∞:=
  ∑'l:ℤ,ENNReal.ofReal (Real.exp (-t*(l:ℝ)^2))*ENNReal.ofReal (‖fourierCoeff f l‖^2)

/-- Actual native heat energy, with its exact half-time normalization. -/
theorem heat_norm (t:ℝ)(ht:0≤t)(f:CircleL2):
    heatMass t f=ENNReal.ofReal (‖circleHeatOperator (t/2) (by positivity) f‖^2):=by
  rw [L2_norm_sq_eq_integral,circle_parseval_ennreal]
  apply tsum_congr
  intro l
  rw [circleHeatOperator_fourierCoeff,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),←Real.exp_nat_mul]
  rw [←ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 3
  push_cast
  ring

theorem kernel_add {ρ Λ t:ℝ}(ht:0<t)(l:ℤ):
    NativeBesselLaplace.kernel ρ (Λ+(l:ℝ)^2) t=
      NativeBesselLaplace.kernel ρ Λ t*ENNReal.ofReal (Real.exp (-t*(l:ℝ)^2)):=by
  have he:Real.exp (-(Λ+(l:ℝ)^2)*t)=Real.exp (-Λ*t)*Real.exp (-t*(l:ℝ)^2):=by
    rw [←Real.exp_add]
    congr 1
    ring
  simp only [NativeBesselLaplace.kernel,he]
  rw [ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
    ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul (Real.exp_pos _).le]
  ac_rfl

/-- Positive heat/Laplace representation of the ACTUAL native massive
Bessel norm, with all Fourier modes and all positive heat times. -/
theorem bessel_norm (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0<ρ)(f:CircleL2):
    ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le f‖^2)=
      ∫⁻t in Ioi (0:ℝ),NativeBesselLaplace.kernel ρ Λ t*heatMass t f:=by
  have hs:=NativeFourierAverage.energy_of_identified Λ ρ hΛ
    (OneInputOperator.besselHalf Λ ρ hΛ hρ.le f) f
    (OneInputOperator.besselHalf_fourierCoeff Λ ρ hΛ hρ.le f)
  rw [←hs.2,ENNReal.ofReal_tsum_of_nonneg
    (fun l=>mul_nonneg (Real.rpow_nonneg (by nlinarith [sq_nonneg (l:ℝ)]) _) (sq_nonneg _)) hs.1]
  have he(l:ℤ):ENNReal.ofReal ((Λ+(l:ℝ)^2)^(-ρ)*‖fourierCoeff f l‖^2)=
      ENNReal.ofReal ((Λ+(l:ℝ)^2)^(-ρ))*ENNReal.ofReal (‖fourierCoeff f l‖^2):=
    ENNReal.ofReal_mul (Real.rpow_nonneg (by nlinarith [sq_nonneg (l:ℝ)]) _)
  simp_rw [he]
  rw [NativeBesselLaplace.spectral hρ (zero_lt_one.trans_le hΛ)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [kernel_add ht]
  simp_rw [mul_assoc]
  exact ENNReal.tsum_mul_left

end SHE.NativeBesselHeatEnergy
