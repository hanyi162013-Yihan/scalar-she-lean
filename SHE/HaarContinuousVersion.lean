module

public import SHE.KolmogorovModification
public import SHE.HaarUnitTimeMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! A genuine continuous version of the actual fixed-terminal Haar
stochastic convolution. Its only stochastic inputs are the universal
terminal Hilbert integral and universal BDG16 inequality. -/
noncomputable section
namespace SHE.HaarContinuousVersion
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal
local instance haarContinuousVersion_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarContinuousVersion_stateSigma : MeasurableSpace LowBands.StateL2 := borel LowBands.StateL2
local instance haarContinuousVersion_stateBorel : BorelSpace LowBands.StateL2 := ⟨rfl⟩

def normalizedTime (h t : ℝ≥0) : ℝ := (min t h:ℝ≥0)/(h:ℝ)

theorem normalizedTime_mem {h : ℝ≥0} (hh0 : 0 < h) (t : ℝ≥0) :
    normalizedTime h t ∈ Icc (0:ℝ) 1 := by
  have hhR : (0:ℝ) < h := by exact_mod_cast hh0
  constructor
  · exact div_nonneg (NNReal.coe_nonneg _) hhR.le
  · apply (div_le_one hhR).mpr
    exact_mod_cast min_le_right t h

theorem continuous_normalizedTime (h : ℝ≥0) : Continuous (normalizedTime h) := by
  unfold normalizedTime
  fun_prop

theorem clock_normalizedTime {h : ℝ≥0} (hh0 : 0 < h) (t : ℝ≥0) :
    HaarUnitTimeMoments.clock h (normalizedTime h t)=min t h := by
  apply NNReal.coe_injective
  rw [HaarUnitTimeMoments.clock_coe h (normalizedTime_mem hh0 t)]
  unfold normalizedTime
  exact mul_div_cancel₀ _ (by exact_mod_cast hh0.ne' : (h:ℝ) ≠ 0)

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)

def version (t : ℝ≥0) (ω : Ω) : LowBands.StateL2 :=
  KolmogorovModification.modification (HaarUnitTimeMoments.process 𝓕 μ h hh hell hM f hf I)
    (normalizedTime h t) ω

theorem continuous_version (hh0 : 0 < h) (ω : Ω) :
    Continuous (fun t => version 𝓕 μ h hh hell hM f hf I t ω) := by
  exact (KolmogorovModification.continuousOn_modification
    (HaarUnitTimeMoments.process 𝓕 μ h hh hell hM f hf I) ω).comp_continuous
    (continuous_normalizedTime h) (normalizedTime_mem hh0)

variable (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
include hBDG

theorem version_measurable (hh0 : 0 < h) (t : ℝ≥0) :
    Measurable (version 𝓕 μ h hh hell hM f hf I t) := by
  exact KolmogorovModification.modification_measurable μ
    (HaarUnitTimeMoments.process 𝓕 μ h hh hell hM f hf I)
    (fun r _ => HaarUnitTimeMoments.process_measurable 𝓕 μ h hh hell hM f hf I r)
    (HaarTerminalMoments.momentConstant_nonneg B M)
    (fun s hs t ht => HaarUnitTimeMoments.increment_moment16 𝓕 μ h hh hell hM f hf I B hBDG hs ht)
    (normalizedTime_mem hh0 t)

/-- At every time, the version equals the original actual stochastic
convolution stopped at h. This is a fixed-time AE assertion, as required
for a modification; the paths of the version are simultaneously continuous. -/
theorem version_ae (hh0 : 0 < h) (t : ℝ≥0) :
    version 𝓕 μ h hh hell hM f hf I t =ᵐ[μ]
      TerminalHaarConvolution.value 𝓕 μ h hh hell hM f hf I (min t h) (min_le_right t h) := by
  have he := KolmogorovModification.modification_ae μ
    (HaarUnitTimeMoments.process 𝓕 μ h hh hell hM f hf I)
    (fun r _ => HaarUnitTimeMoments.process_measurable 𝓕 μ h hh hell hM f hf I r)
    (HaarTerminalMoments.momentConstant_nonneg B M)
    (fun s hs t ht => HaarUnitTimeMoments.increment_moment16 𝓕 μ h hh hell hM f hf I B hBDG hs ht)
    (normalizedTime_mem hh0 t)
  change version 𝓕 μ h hh hell hM f hf I t =ᵐ[μ]
    TerminalHaarConvolution.value 𝓕 μ h hh hell hM f hf I
      (HaarUnitTimeMoments.clock h (normalizedTime h t)) _ at he
  simpa only [clock_normalizedTime hh0] using he

theorem version_ae_of_le (hh0 : 0 < h) (t : ℝ≥0) (ht : t ≤ h) :
    version 𝓕 μ h hh hell hM f hf I t =ᵐ[μ]
      TerminalHaarConvolution.value 𝓕 μ h hh hell hM f hf I t ht := by
  simpa only [min_eq_left ht] using version_ae 𝓕 μ h hh hell hM f hf I B hBDG hh0 t

theorem version_joint_measurable (hh0 : 0 < h) :
    Measurable (fun p : ℝ≥0 × Ω => version 𝓕 μ h hh hell hM f hf I p.1 p.2) := by
  exact measurable_uncurry_of_continuous_of_measurable
    (continuous_version 𝓕 μ h hh hell hM f hf I hh0)
    (version_measurable 𝓕 μ h hh hell hM f hf I B hBDG hh0)

end SHE.HaarContinuousVersion
