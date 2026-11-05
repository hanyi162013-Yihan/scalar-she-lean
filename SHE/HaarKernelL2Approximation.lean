module

public import SHE.HaarKernelApproximation
public import SHE.HaarIntegrandEnergy
public import SHE.TimeMeasureRestriction
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarKernelL2Approximation
open MeasureTheory Set Filter AddCircle CircleHeat FiniteHaar PredictableL2 HaarKernelApproximation
open scoped NNReal ENNReal Topology
local instance haarKernelL2Approximation_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance haarKernelL2Approximation_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarKernelL2Approximation_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance haarKernelL2Approximation_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance haarKernelL2Approximation_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarKernelL2Approximation_columnsBorel : BorelSpace Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

def measure (μ : Measure Ω) (h : ℝ≥0) : Measure (ℝ≥0 × (ℝ≥0 × Ω)) :=
  (timeMeasure h).prod ((timeMeasure h).prod μ)

def raw {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (p : ℝ≥0 × (ℝ≥0 × Ω)) : Columns :=
  RealHaarIntegrand.kernel ell M hell ((p.1:ℝ)-(p.2.1:ℝ),f p.2)

def approx {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (n : ℕ) (p : ℝ≥0 × (ℝ≥0 × Ω)) : Columns :=
  approximant ell M hell n p.1 p.2.1 (f p.2)

theorem raw_measurable {ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → EllipticField ell M}
    (hf : Measurable f) : Measurable (raw hell f) :=
  (RealHaarIntegrand.kernel_measurable ell M hell).comp
    (((measurable_coe_nnreal_real.comp measurable_fst).sub
      (measurable_coe_nnreal_real.comp measurable_snd.fst)).prodMk (hf.comp measurable_snd))

theorem approx_measurable {ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → EllipticField ell M}
    (hf : Measurable f) (n : ℕ) : Measurable (approx hell f n) :=
  (approximant_measurable ell M hell n).comp
    (((measurable_coe_nnreal_real.comp measurable_fst).prodMk
      (measurable_coe_nnreal_real.comp measurable_snd.fst)).prodMk (hf.comp measurable_snd))

theorem causal_lintegral {ell M : ℝ} (hell : 0 < ell) (μ : Measure Ω)
    (f : ℝ≥0 × Ω → EllipticField ell M) {h t : ℝ≥0} (ht : t ≤ h) :
    (∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖raw hell f (t,(s,ω))‖^2) ∂μ ∂timeMeasure h)=
      ∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖raw hell f (t,(s,ω))‖^2) ∂μ ∂timeMeasure t := by
  rw [← timeMeasure_restrict ht,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with s hs
  by_cases hst : s ≤ t
  · rw [Set.indicator_of_mem (show s ∈ Ioc 0 t from ⟨hs.1,hst⟩)]
  · rw [Set.indicator_of_notMem (show s ∉ Ioc 0 t from fun hh => hst hh.2)]
    have hτ : (t:ℝ)-(s:ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hst))
    simp only [raw,kernel_zero hell hτ,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero,lintegral_zero]

theorem raw_energy_finite {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {f : ℝ≥0 × Ω → EllipticField ell M} (hf : Measurable f) :
    (∫⁻ p,ENNReal.ofReal (‖raw hell f p‖^2) ∂measure μ h) < ∞ := by
  have hm : Measurable (fun p => ENNReal.ofReal (‖raw hell f p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((raw_measurable hell hf).norm.pow_const 2)
  change (∫⁻ p,ENNReal.ofReal (‖raw hell f p‖^2) ∂(timeMeasure h).prod ((timeMeasure h).prod μ)) < ∞
  rw [lintegral_prod _ hm.aemeasurable]
  have he : (∫⁻ t,∫⁻ p,ENNReal.ofReal (‖raw hell f (t,p)‖^2) ∂(timeMeasure h).prod μ ∂timeMeasure h)=
      ∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal
        (‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))‖^2) ∂μ ∂timeMeasure t ∂timeMeasure h := by
    apply lintegral_congr_ae
    filter_upwards [timeMeasure_ae_mem h] with t ht
    have hmt : Measurable (fun p : ℝ≥0 × Ω => ENNReal.ofReal (‖raw hell f (t,p)‖^2)) :=
      hm.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hmt.aemeasurable, causal_lintegral hell μ f ht.2]
    rfl
  rw [he]
  exact HaarIntegrandEnergy.total_energy_finite μ hell hM h hh f

/-- The actual adapted finite time-cell kernels converge in full
time/probability Hilbert--Schmidt L² energy, with the literal common-Haar
nonlinearity retained throughout. -/
theorem approximation_energy_tendsto {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {f : ℝ≥0 × Ω → EllipticField ell M} (hf : Measurable f) :
    Tendsto (fun n => ∫⁻ p,ENNReal.ofReal (‖approx hell f n p-raw hell f p‖^2) ∂measure μ h)
      atTop (𝓝 (0:ℝ≥0∞)) := by
  have hraw := raw_measurable hell hf
  have htime : ∀ᵐ p ∂measure μ h,0 < p.1 :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem h).mono (fun _ hh => hh.1))
  have hfinite : (∫⁻ p,ENNReal.ofReal 4*ENNReal.ofReal (‖raw hell f p‖^2) ∂measure μ h) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (raw_energy_finite hell hM μ h hh hf).ne
  have he := tendsto_lintegral_of_dominated_convergence
    (μ := measure μ h) (fun p => ENNReal.ofReal 4*ENNReal.ofReal (‖raw hell f p‖^2))
    (F := fun n p => ENNReal.ofReal (‖approx hell f n p-raw hell f p‖^2)) (f := fun _ => 0)
    (fun n => ENNReal.continuous_ofReal.measurable.comp (((approx_measurable hell hf n).sub hraw).norm.pow_const 2))
    (fun n => htime.mono (fun p hp => by
      change ENNReal.ofReal (‖approx hell f n p-raw hell f p‖^2) ≤
        ENNReal.ofReal 4*ENNReal.ofReal (‖raw hell f p‖^2)
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      exact ENNReal.ofReal_le_ofReal (approximant_difference_bound (t := p.1) (s := p.2.1)
        hell (by exact_mod_cast hp) (f p.2) n)))
    hfinite (htime.mono (fun p hp => by
      have ht : Tendsto (fun n => approx hell f n p-raw hell f p) atTop (𝓝 (0 : Columns)) := by
        simpa only [approx,raw,sub_self] using
          (approximant_tendsto (t := p.1) (s := p.2.1) hell (by exact_mod_cast hp) (f p.2)).sub
            (tendsto_const_nhds (x := raw hell f p))
      have hn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht.norm.pow 2)
      change Tendsto (fun n => ENNReal.ofReal (‖approx hell f n p-raw hell f p‖^2))
        atTop (𝓝 (ENNReal.ofReal (‖(0 : Columns)‖^2))) at hn
      simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero] using hn))
  simpa only [lintegral_zero] using he

end SHE.HaarKernelL2Approximation
