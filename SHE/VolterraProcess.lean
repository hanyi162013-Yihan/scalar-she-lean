module

public import SHE.VolterraProcessEnergy
public import SHE.VolterraPredictable
public import SHE.ProcessEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.VolterraProcess
open MeasureTheory Set PredictableL2 LowBands
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2 := borel StateL2
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (h : ℝ≥0) {Λ : ℝ} (hΛ : 0 ≤ Λ) (U : ℝ≥0 → Ω → StateL2)
variable (ha : StronglyAdapted 𝓕 U) (hc : ∀ ω,Continuous (fun t => U t ω))
variable (v : Process (E := StateL2) 𝓕 μ h)
variable (hv : v =ᵐ[energyMeasure μ h] Function.uncurry U)

def function (p : ℝ≥0 × Ω) : StateL2 := VolterraPath.value Λ (fun s => U s p.2) p.1

include ha hc hv hΛ in
/-- The literal deterministic causal heat convolution belongs to the
complete predictable L² space whenever its continuous adapted input does. -/
theorem memLp :
    @MemLp _ _ 𝓕.predictable _ _ (function (Λ := Λ) U) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have hp := VolterraPredictable.value_predictable 𝓕 Λ U ha hc
  change StronglyMeasurable[𝓕.predictable] (function (Λ := Λ) U) at hp
  have hm := hp.mono (predictable_le_product 𝓕)
  have hn : Measurable (fun p : ℝ≥0 × Ω => ENNReal.ofReal (‖function (Λ := Λ) U p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp (hm.measurable.norm.pow_const 2)
  have hUenergy : (∫⁻ t,∫⁻ ω,ENNReal.ofReal (‖U t ω‖^2) ∂μ ∂timeMeasure h)=
      ENNReal.ofReal (‖v‖^2) := by
    rw [process_lintegral_energy]
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hv] with t ht
    apply lintegral_congr_ae
    filter_upwards [ht] with ω hω
    rw [hω]
    rfl
  have hE : (∫⁻ p,ENNReal.ofReal (‖function (Λ := Λ) U p‖^2) ∂energyMeasure μ h) < ∞ := by
    change (∫⁻ p,ENNReal.ofReal (‖function (Λ := Λ) U p‖^2) ∂(timeMeasure h).prod μ) < ∞
    rw [lintegral_prod _ hn.aemeasurable]
    have hb := VolterraProcessEnergy.total_energy_bound 𝓕 μ Λ hΛ U ha hc h
    rw [hUenergy] at hb
    exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hL : MemLp (function (Λ := Λ) U) 2 (energyMeasure μ h) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    exact ⟨(hm.norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun p => sq_nonneg ‖function (Λ := Λ) U p‖))).mpr hE⟩
  change eLpNorm (function (Λ := Λ) U) 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕)) < ∞
  rw [eLpNorm_trim (predictable_le_product 𝓕) hp]
  exact hL

/-- Actual causal convolution as a predictable L² process. -/
def process : Process (E := StateL2) 𝓕 μ h :=
  (memLp 𝓕 μ h hΛ U ha hc v hv).toLp (function (Λ := Λ) U)

theorem process_ae : process 𝓕 μ h hΛ U ha hc v hv =ᵐ[energyMeasure μ h]
    function (Λ := Λ) U :=
  ae_eq_of_ae_eq_trim (memLp 𝓕 μ h hΛ U ha hc v hv).coeFn_toLp

end SHE.VolterraProcess
