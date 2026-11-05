module
public import SHE.DampedEnergy
public import SHE.OneInputOperator
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBesselLaplace
open Set MeasureTheory Real AddCircle StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

def kernel (ρ m t:ℝ):ℝ≥0∞:=
  ENNReal.ofReal (Real.exp (-m*t)*t^(ρ-1))*(ENNReal.ofReal (Real.Gamma ρ))⁻¹

theorem kernel_measurable (ρ m:ℝ):Measurable (kernel ρ m):=by
  unfold kernel
  fun_prop

/-- Exact positive Laplace measure for the native massive Fourier
symbol. This fixes the native spatial frequency and normalization. -/
theorem symbol {ρ m:ℝ}(hρ:0<ρ)(hm:0<m):
    (∫⁻t in Ioi (0:ℝ),kernel ρ m t)=ENNReal.ofReal (m^(-ρ)):=by
  have hg:0<Real.Gamma ρ:=Real.Gamma_pos_of_pos hρ
  have hi:IntegrableOn (fun t:ℝ=>Real.exp (-m*t)*t^(ρ-1)) (Ioi 0):=by
    convert! damped_power_integrable (Λ:=m/2) (by positivity) hρ using 1
    funext t
    congr 2
    ring
  have he:(∫t:ℝ in Ioi 0,Real.exp (-m*t)*t^(ρ-1))=m^(-ρ)*Real.Gamma ρ:=by
    rw [show (fun t:ℝ=>Real.exp (-m*t)*t^(ρ-1))=
      (fun t:ℝ=>t^(ρ-1)*Real.exp (-(m*t))) by funext t;ring]
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hρ hm,one_div,←Real.rpow_neg_eq_inv_rpow]
  have hn:∀ᵐt:ℝ∂volume.restrict (Ioi 0),0≤Real.exp (-m*t)*t^(ρ-1):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
  simp only [kernel]
  rw [lintegral_mul_const _ (by fun_prop)]
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn,he,
    ENNReal.ofReal_mul (Real.rpow_nonneg hm.le _),mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hg) ENNReal.ofReal_ne_top,mul_one]

/-- Tonelli for the genuine positive native Fourier heat energies.
All modes are retained; there is no conditionally convergent kernel sum. -/
theorem spectral {ρ Λ:ℝ}(hρ:0<ρ)(hΛ:0<Λ)(a:ℤ→ℝ≥0∞):
    (∑'l:ℤ,ENNReal.ofReal ((Λ+(l:ℝ)^2)^(-ρ))*a l)=
      ∫⁻t in Ioi (0:ℝ),∑'l:ℤ,kernel ρ (Λ+(l:ℝ)^2) t*a l:=by
  rw [lintegral_tsum]
  · apply tsum_congr
    intro l
    rw [lintegral_mul_const _ (kernel_measurable ρ (Λ+(l:ℝ)^2)),symbol hρ (by nlinarith [sq_nonneg (l:ℝ)])]
  · intro l
    exact (kernel_measurable ρ (Λ+(l:ℝ)^2)).aemeasurable.mul_const _

end SHE.NativeBesselLaplace
