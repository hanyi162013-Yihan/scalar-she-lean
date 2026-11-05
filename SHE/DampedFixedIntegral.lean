module

public import SHE.DampedStochasticConvolution
public import SHE.HaarFixedTerminalEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.DampedFixedIntegral
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel CircleL2
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

def kernel {Λ ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (t : ℝ≥0) (p : ℝ≥0 × Ω) : RealHaarIntegrand.Columns :=
  DampedHeatKernel.kernel Λ ell M hell ((t:ℝ)-(p.1:ℝ),f p)

theorem kernel_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {Λ ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → EllipticField ell M}
    (hf : StronglyMeasurable[𝓕.predictable] f) (t : ℝ≥0) :
    StronglyMeasurable[𝓕.predictable] (kernel (Λ := Λ) hell f t) :=
  ((DampedHeatKernel.kernel_measurable Λ ell M hell).comp
    ((measurable_const.sub (PredictableClock.real_time_measurable 𝓕)).prodMk hf.measurable)).stronglyMeasurable

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
variable {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

include hh hΛ hM hf in
theorem kernel_memLp (t : ℝ≥0) (ht : t ≤ h) :
    @MemLp _ _ 𝓕.predictable _ _ (kernel (Λ := Λ) hell f t) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have hs := kernel_predictable 𝓕 (Λ := Λ) hell hf t
  have ha := hs.mono (predictable_le_product 𝓕)
  have hnorm : Measurable (fun p => ENNReal.ofReal (‖kernel (Λ := Λ) hell f t p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp (ha.measurable.norm.pow_const 2)
  have hE : (∫⁻ p,ENNReal.ofReal (‖kernel (Λ := Λ) hell f t p‖^2) ∂energyMeasure μ h) < ∞ := by
    change (∫⁻ p,ENNReal.ofReal (‖kernel (Λ := Λ) hell f t p‖^2) ∂(timeMeasure h).prod μ) < ∞
    rw [lintegral_prod _ hnorm.aemeasurable]
    apply lt_of_le_of_lt _ ((HaarFixedTerminalEnergy.fixed_energy_bound μ hell hM hh ht f).trans_lt ENNReal.ofReal_lt_top)
    apply lintegral_mono
    intro s
    apply lintegral_mono
    intro ω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
      (DampedHeatKernel.kernel_norm_le (t := (t:ℝ)-(s:ℝ)) hΛ hell (f (s,ω))) 2)
  have hL : MemLp (kernel (Λ := Λ) hell f t) 2 (energyMeasure μ h) := by
    apply (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mpr
    exact ⟨(ha.norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun p => sq_nonneg ‖kernel (Λ := Λ) hell f t p‖))).mpr hE⟩
  change eLpNorm (kernel (Λ := Λ) hell f t) 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕)) < ∞
  rw [eLpNorm_trim (predictable_le_product 𝓕) hs]
  exact hL

def input (t : ℝ≥0) (ht : t ≤ h) : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h :=
  (kernel_memLp 𝓕 μ h hh hΛ hell hM f hf t ht).toLp (kernel (Λ := Λ) hell f t)

theorem input_ae (t : ℝ≥0) (ht : t ≤ h) :
    input 𝓕 μ h hh hΛ hell hM f hf t ht =ᵐ[energyMeasure μ h] kernel (Λ := Λ) hell f t :=
  ae_eq_of_ae_eq_trim (kernel_memLp 𝓕 μ h hh hΛ hell hM f hf t ht).coeFn_toLp

theorem input_stopped (t : ℝ≥0) (ht : t ≤ h) :
    ∀ᵐ p ∂energyMeasure μ h,t < p.1 → input 𝓕 μ h hh hΛ hell hM f hf t ht p=0 := by
  filter_upwards [input_ae 𝓕 μ h hh hΛ hell hM f hf t ht] with p hp hpt
  rw [hp,kernel,DampedHeatKernel.kernel_zero hell
    (sub_nonpos.mpr (by exact_mod_cast hpt.le))]

variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)

/-- Actual damped fixed-terminal stochastic convolution at every time. -/
def value (t : ℝ≥0) (ht : t ≤ h) : Lp LowBands.StateL2 2 μ :=
  I.integral (input 𝓕 μ h hh hΛ hell hM f hf t ht)

theorem adapted_version (t : ℝ≥0) (ht : t ≤ h) :
    ∃ Z : Ω → LowBands.StateL2,StronglyMeasurable[𝓕 t] Z ∧
      value 𝓕 μ h hh hΛ hell hM f hf I t ht =ᵐ[μ] Z :=
  I.adapted t _ (input_stopped 𝓕 μ h hh hΛ hell hM f hf t ht)

theorem centered (t : ℝ≥0) (ht : t ≤ h) :
    (∫ ω,value 𝓕 μ h hh hΛ hell hM f hf I t ht ω ∂μ)=0 := I.centered _

end SHE.DampedFixedIntegral
