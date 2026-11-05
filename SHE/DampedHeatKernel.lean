module

public import SHE.HaarKernelApproximation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.DampedHeatKernel
open MeasureTheory Set Filter CircleHeat FiniteHaar HaarKernelApproximation ApproximationClock
open scoped NNReal ENNReal Topology
local instance dampedHeatKernel_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance dampedHeatKernel_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance dampedHeatKernel_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance dampedHeatKernel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance dampedHeatKernel_columnsSigma : MeasurableSpace Columns := borel Columns
local instance dampedHeatKernel_columnsBorel : BorelSpace Columns := ⟨rfl⟩

def kernel (Λ ell M : ℝ) (hell : 0 < ell) (p : ℝ × EllipticField ell M) : Columns :=
  Real.exp (-Λ*p.1) • RealHaarIntegrand.kernel ell M hell p

def approximant (Λ ell M : ℝ) (hell : 0 < ell) (n : ℕ) (t s : ℝ) (f : EllipticField ell M) : Columns :=
  Real.exp (-Λ*(right n t-s)) • HaarKernelApproximation.approximant ell M hell n t s f

theorem kernel_measurable (Λ ell M : ℝ) (hell : 0 < ell) : Measurable (kernel Λ ell M hell) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).smul
    (RealHaarIntegrand.kernel_measurable ell M hell)

theorem approximant_measurable (Λ ell M : ℝ) (hell : 0 < ell) (n : ℕ) :
    Measurable (fun p : (ℝ × ℝ) × EllipticField ell M => approximant Λ ell M hell n p.1.1 p.1.2 p.2) :=
  (Real.measurable_exp.comp (measurable_const.mul
    (((right_measurable n).comp measurable_fst.fst).sub measurable_fst.snd))).smul
      (HaarKernelApproximation.approximant_measurable ell M hell n)

theorem kernel_zero {Λ ell M t : ℝ} (hell : 0 < ell) (ht : t ≤ 0) (f : EllipticField ell M) :
    kernel Λ ell M hell (t,f)=0 := by
  rw [kernel,HaarKernelApproximation.kernel_zero hell ht,smul_zero]

theorem kernel_norm_le {Λ ell M t : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (f : EllipticField ell M) :
    ‖kernel Λ ell M hell (t,f)‖ ≤ ‖RealHaarIntegrand.kernel ell M hell (t,f)‖ := by
  by_cases ht : t ≤ 0
  · rw [kernel_zero hell ht,HaarKernelApproximation.kernel_zero hell ht,norm_zero]
  · have he : Real.exp (-Λ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [le_of_not_ge ht])
    rw [kernel,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)

theorem approximant_norm_le {Λ ell M t s : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell)
    (ht : 0 < t) (f : EllipticField ell M) (n : ℕ) :
    ‖approximant Λ ell M hell n t s f‖ ≤ ‖kernel Λ ell M hell (t-s,f)‖ := by
  by_cases hs : s ≤ left n t
  · have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (HaarKernelApproximation.approximant_norm_sq_le (s := s) hell ht f n)
    have he : Real.exp (-Λ*(right n t-s)) ≤ Real.exp (-Λ*(t-s)) :=
      Real.exp_le_exp.mpr (by nlinarith [(right_bounds n ht.le).1])
    rw [approximant,kernel,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he hn (norm_nonneg _) (Real.exp_pos _).le
  · simp only [approximant,HaarKernelApproximation.approximant,ite_eq_right hs,
      smul_zero,norm_zero,norm_nonneg]

theorem approximant_tendsto {Λ ell M t s : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (f : EllipticField ell M) :
    Tendsto (fun n => approximant Λ ell M hell n t s f) atTop (𝓝 (kernel Λ ell M hell (t-s,f))) := by
  have he : Tendsto (fun n => Real.exp (-Λ*(right n t-s))) atTop (𝓝 (Real.exp (-Λ*(t-s)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((right_tendsto ht.le).sub_const s))
  exact he.smul (HaarKernelApproximation.approximant_tendsto hell ht f)

end SHE.DampedHeatKernel
