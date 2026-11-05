module

public import SHE.HaarFixedTerminalEnergy
public import SHE.StandardTerminalIto

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FixedHaarIntegral
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal
local instance fixedHaarIntegral_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance fixedHaarIntegral_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance fixedHaarIntegral_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance fixedHaarIntegral_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance fixedHaarIntegral_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

def kernel {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (t : ℝ≥0) (p : ℝ≥0 × Ω) : RealHaarIntegrand.Columns :=
  RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)

theorem kernel_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → EllipticField ell M}
    (hf : StronglyMeasurable[𝓕.predictable] f) (t : ℝ≥0) :
    StronglyMeasurable[𝓕.predictable] (kernel hell f t) :=
  ((RealHaarIntegrand.kernel_measurable ell M hell).comp
    ((measurable_const.sub (PredictableClock.real_time_measurable 𝓕)).prodMk hf.measurable)).stronglyMeasurable

theorem kernel_memLp (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {f : ℝ≥0 × Ω → EllipticField ell M} (hf : StronglyMeasurable[𝓕.predictable] f)
    (t : ℝ≥0) (ht : t ≤ h) :
    @MemLp _ _ 𝓕.predictable _ _ (kernel hell f t) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have hs := kernel_predictable 𝓕 hell hf t
  have ha := hs.mono (predictable_le_product 𝓕)
  have hnorm : Measurable (fun p => ENNReal.ofReal (‖kernel hell f t p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp (ha.measurable.norm.pow_const 2)
  have hE : (∫⁻ p,ENNReal.ofReal (‖kernel hell f t p‖^2) ∂energyMeasure μ h) < ∞ := by
    change (∫⁻ p,ENNReal.ofReal (‖kernel hell f t p‖^2) ∂(timeMeasure h).prod μ) < ∞
    rw [lintegral_prod _ hnorm.aemeasurable]
    exact (HaarFixedTerminalEnergy.fixed_energy_bound μ hell hM hh ht f).trans_lt ENNReal.ofReal_lt_top
  have hL : MemLp (kernel hell f t) 2 (energyMeasure μ h) := by
    apply (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mpr
    refine ⟨?_,(hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun p => sq_nonneg ‖kernel hell f t p‖))).mpr hE⟩
    exact (ha.norm.pow 2).aestronglyMeasurable
  change eLpNorm (kernel hell f t) 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕)) < ∞
  rw [eLpNorm_trim (predictable_le_product 𝓕) hs]
  exact hL

def input (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (t : ℝ≥0) (ht : t ≤ h) : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h :=
  (kernel_memLp 𝓕 μ h hh hell hM hf t ht).toLp (kernel hell f t)

theorem input_ae (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (t : ℝ≥0) (ht : t ≤ h) :
    input 𝓕 μ h hh hell hM f hf t ht =ᵐ[energyMeasure μ h] kernel hell f t :=
  ae_eq_of_ae_eq_trim (kernel_memLp 𝓕 μ h hh hell hM hf t ht).coeFn_toLp

theorem input_stopped (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (t : ℝ≥0) (ht : t ≤ h) :
    ∀ᵐ p ∂energyMeasure μ h,t < p.1 → input 𝓕 μ h hh hell hM f hf t ht p=0 := by
  filter_upwards [input_ae 𝓕 μ h hh hell hM f hf t ht] with p hp hpt
  rw [hp,kernel,HaarKernelApproximation.kernel_zero hell
    (sub_nonpos.mpr (by exact_mod_cast hpt.le))]

end SHE.FixedHaarIntegral
