module

public import SHE.TimeDilationEquivalence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory Set Filter PredictableL2
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

theorem processEquivalence_symm_stopped (l : ℝ≥0)
    (v : Process (E:=C) 𝓕 μ h)
    (hv : ∀ᵐ p ∂energyMeasure μ h,l<p.1→v p=0) :
    ∀ᵐ p ∂energyMeasure μ (c*h),clock c hc l<p.1→
      (processEquivalence 𝓕 μ c hc h).symm v p=0 := by
  have hrev:=ScaledLpPull.inverse_preserving (energyMeasure μ h) (energyMeasure μ (c*h))
    (c:ℝ) hc (ambientEquiv c hc) (energyMeasure_clock_preserving c hc h μ)
  have hh:=hrev.quasiMeasurePreserving.ae hv
  have hh':=(Measure.ae_ennreal_smul_measure_iff
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (show (0:ℝ)<c from hc)))).mp hh
  filter_upwards [processEquivalence_symm_ae 𝓕 μ c hc h v,hh'] with p hp hs hlt
  have hlt' : l<(clock c hc).symm p.1 := by
    simpa only [OrderIso.symm_apply_apply] using (clock c hc).symm.strictMono hlt
  change l<(clock c hc).symm p.1→v ((clock c hc).symm p.1,p.2)=0 at hs
  rw [hp,hs hlt',smul_zero]

/-- Inverting a deterministic Brownian clock preserves the SAME
terminal integral. The normalized predictable equivalence is onto,
and its inverse transports stopped adaptedness exactly. -/
def inverseIntegral
    (J : StandardTerminalIto (C:=C) (E:=E) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    StandardTerminalIto (C:=C) (E:=E) 𝓕 μ h where
  integral:=J.integral.comp (processEquivalence 𝓕 μ c hc h).symm.toLinearIsometry
  adapted l v hv:=by
    obtain ⟨Z,hZ,he⟩:=J.adapted (clock c hc l) _
      (processEquivalence_symm_stopped 𝓕 μ c hc h l v hv)
    exact ⟨Z,(filtration_clock 𝓕 (clock c hc) l) ▸ hZ,he⟩
  centered v:=J.centered _

/-- Reclocking the derived inverse integral recovers every original
native-clock terminal Itô value exactly, not only in distribution. -/
theorem integral_inverseIntegral
    (J : StandardTerminalIto (C:=C) (E:=E) (filtration 𝓕 (clock c hc)) μ (c*h))
    (v : Process (E:=C) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    (integral 𝓕 μ c hc h (inverseIntegral 𝓕 μ c hc h J)).integral v=J.integral v := by
  change J.integral ((processEquivalence 𝓕 μ c hc h).symm (processIsometry 𝓕 μ c hc h v))=J.integral v
  rw [← processEquivalence_apply,LinearIsometryEquiv.symm_apply_apply]

/-- Exact samplewise bracket identity for the inverse Brownian clock. -/
theorem inverse_bracket_ae (v : Process (E:=C) 𝓕 μ h) :
    ∀ᵐ ω ∂μ,(∫⁻ t,ENNReal.ofReal (‖(processEquivalence 𝓕 μ c hc h).symm v (t,ω)‖^2)
      ∂timeMeasure (c*h))=∫⁻ s,ENNReal.ofReal (‖v (s,ω)‖^2) ∂timeMeasure h := by
  have he:=bracket_ae 𝓕 μ c hc h ((processEquivalence 𝓕 μ c hc h).symm v)
  have hp : processIsometry 𝓕 μ c hc h ((processEquivalence 𝓕 μ c hc h).symm v)=v := by
    rw [← processEquivalence_apply,LinearIsometryEquiv.apply_symm_apply]
  rw [hp] at he
  filter_upwards [he] with ω hω
  exact hω.symm

theorem inverse_bdgPower (p : ℕ)
    (J : StandardTerminalIto (C:=C) (E:=E) (filtration 𝓕 (clock c hc)) μ (c*h))
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    StandardTerminalBDGPower p (inverseIntegral 𝓕 μ c hc h J) B := by
  intro v
  apply (hBDG ((processEquivalence 𝓕 μ c hc h).symm v)).trans_eq
  congr 1
  apply lintegral_congr_ae
  filter_upwards [inverse_bracket_ae 𝓕 μ c hc h v] with ω hω
  rw [hω]

end SHE.PredictableTimeDilation
