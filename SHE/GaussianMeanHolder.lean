module

public import SHE.ProfileStability

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.GaussianMeanHolder
open Set MeasureTheory ProbabilityTheory GaussianProfile ProfileVariance ProfileStability
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- Gaussian averaging preserves the coefficient's original Holder
modulus in the mean, with constant one, even at zero variance. -/
theorem mean_holder {a : ℝ→ℝ} (ha : Measurable a) {M H β : ℝ}
    (haB : ∀ z,|a z|≤M) (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (m n v : ℝ) :
    |gaussianAverage a m v-gaussianAverage a n v|≤H*|m-n|^β := by
  have hi (c : ℝ) : Integrable (fun z=>a (c+z)) (gaussianReal 0 v.toNNReal):=
    (integrable_const M).mono' (ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using haB (c+z)))
  unfold gaussianAverage
  rw [←integral_sub (hi m) (hi n),←Real.norm_eq_abs]
  have hh:=norm_integral_le_of_norm_le (f:=fun z=>a (m+z)-a (n+z))
    (μ:=gaussianReal 0 v.toNNReal) (integrable_const (H*|m-n|^β))
    (ae_of_all _ (fun z : ℝ=>by
      simpa only [Real.norm_eq_abs,add_sub_add_right_eq_sub] using hholder (m+z) (n+z)))
  simpa only [integral_const,probReal_univ,one_smul] using hh

/-- In the actual two-input Gaussian update, the physical mean now
costs its Holder modulus with NO negative time power. The variance
source keeps its sharp heat-square Volterra factor. -/
theorem update_two_inputs {a : ℝ→ℝ} {φ ψ c d : ℝ×StoppedFourier.HeatCircle→ℝ}
    {ell M Ua H β r : ℝ} (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0<ell) (hM : 0≤M) (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hr : 0<r) (hr1 : r≤1) (haB : ∀ z,|a z|≤Ua)
    (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (hcl : ∀ s∈Ioo 0 r,∀ y,ell≤c (s,y))
    (hcu : ∀ s∈Ioo 0 r,∀ y,c (s,y)≤M)
    (hdl : ∀ s∈Ioo 0 r,∀ y,ell≤d (s,y))
    (hdu : ∀ s∈Ioo 0 r,∀ y,d (s,y)≤M) (x : StoppedFourier.HeatCircle) :
    |profileUpdate a φ c r x-profileUpdate a ψ d r x|≤
      H*|φ (r,x)-ψ (r,x)|^β+
      (varianceConstant ell H β*r^((β-2)/4))*|varianceMap c r x-varianceMap d r x| := by
  have hvc:=varianceMap_elliptic hc hr hr1 hell.le hM hcl hcu x
  have hvd:=varianceMap_elliptic hd hr hr1 hell.le hM hdl hdu x
  have hlow : 0<lowerConstant*ell:=mul_pos lowerConstant_pos hell
  have hv:=mean_holder ha haB hholder (φ (r,x)) (ψ (r,x)) (varianceMap c r x)
  have hw:=gaussianAverage_variance_lipschitz ha haB hH hβ (by linarith : β≤2)
    (mul_pos hlow (Real.rpow_pos_of_pos hr _)) hvc.1 hvd.1 hholder (ψ (r,x))
  have hp : (lowerConstant*ell*r^(1/2:ℝ))^(β/2-1)=
      (lowerConstant*ell)^(β/2-1)*r^((β-2)/4) := by
    rw [Real.mul_rpow hlow.le (Real.rpow_nonneg hr.le _),←Real.rpow_mul hr.le]
    congr 2
    ring
  rw [hp] at hw
  have hw' : |gaussianAverage a (ψ (r,x)) (varianceMap c r x)-
      gaussianAverage a (ψ (r,x)) (varianceMap d r x)|≤
      (varianceConstant ell H β*r^((β-2)/4))*|varianceMap c r x-varianceMap d r x| := by
    simpa only [varianceConstant,mul_assoc] using hw
  exact (abs_sub_le _ (gaussianAverage a (ψ (r,x)) (varianceMap c r x)) _).trans
    (add_le_add hv hw')

end SHE.GaussianMeanHolder
