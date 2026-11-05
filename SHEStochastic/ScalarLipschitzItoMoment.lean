module

public import SHEStochastic.ScalarLipschitzWeightedMoment
public import SHE.StandardTerminalBDGPower

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.ScalarLipschitzItoMoment
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

def moment (p : ℕ) (Z : Ω → E) (μ : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω,ENNReal.ofReal (‖Z ω‖^p) ∂μ

omit [InnerProductSpace ℝ E] [IsProbabilityMeasure μ] in
theorem moment_congr {p : ℕ} {Z V : Ω → E} (h : Z=ᵐ[μ] V) :
    moment p Z μ=moment p V μ :=
  lintegral_congr_ae (h.fun_comp fun z => ENNReal.ofReal (‖z‖^p))

theorem moment_of_density
    (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (B : ℝ≥0) (hJ : StandardTerminalBDGPower 8 J B)
    (u : Process (E := C) F μ H)
    (k : ℝ≥0 → ℝ≥0∞) (hk : Measurable k)
    (f : ℝ≥0×Ω → ℝ≥0∞) (hf : Measurable f) (M : ℝ≥0∞)
    (hM : ∀ᵐ s ∂timeMeasure H,(∫⁻ ω,(f (s,ω))^8 ∂μ)≤M)
    (hu : ∀ᵐ p ∂energyMeasure μ H, ENNReal.ofReal (‖u p‖^2)≤k p.1*f p) :
    moment 16 (J.integral u) μ≤(B : ℝ≥0∞)*(∫⁻ s,k s ∂timeMeasure H)^8*M := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hu
  have hb : ∀ᵐ ω ∂μ,
      (∫⁻ s,ENNReal.ofReal (‖u (s,ω)‖^2) ∂timeMeasure H)^8 ≤
        (∫⁻ s,k s*f (s,ω) ∂timeMeasure H)^8 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
    exact pow_le_pow_left' (lintegral_mono_ae hω) 8
  calc
    _ ≤ (B : ℝ≥0∞)*(∫⁻ ω,(∫⁻ s,ENNReal.ofReal (‖u (s,ω)‖^2) ∂timeMeasure H)^8 ∂μ) :=
      hJ u
    _ ≤ (B : ℝ≥0∞)*(∫⁻ ω,(∫⁻ s,k s*f (s,ω) ∂timeMeasure H)^8 ∂μ) :=
      mul_le_mul_right (lintegral_mono_ae hb) _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_right
        (ScalarLipschitzWeightedMoment.weighted_eighth (timeMeasure H) μ k hk f hf M hM) _

omit [InnerProductSpace ℝ C] in
/-- Derive integrability of a genuine input from its causal envelope
and a uniform second moment on each time fibre. -/
theorem integrable_of_density
    (v : ℝ≥0×Ω → C) (hv : StronglyMeasurable v)
    (k : ℝ≥0 → ℝ≥0∞) (hk : Measurable k)
    (f : ℝ≥0×Ω → ℝ≥0∞) (hf : Measurable f) (M : ℝ≥0∞) (hMtop : M≠⊤)
    (hM : ∀ᵐ s ∂timeMeasure H,(∫⁻ ω,f (s,ω) ∂μ)≤M)
    (hkm : (∫⁻ s,k s ∂timeMeasure H)≠⊤)
    (h : ∀ᵐ p ∂energyMeasure μ H, ENNReal.ofReal (‖v p‖^2)≤k p.1*f p) :
    Integrable (fun p => ‖v p‖^2) (energyMeasure μ H) := by
  refine ⟨(hv.norm.pow 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mpr ?_⟩
  have hm : Measurable (fun p : ℝ≥0×Ω => k p.1*f p) := (hk.comp measurable_fst).mul hf
  have hfin : (∫⁻ p,ENNReal.ofReal (‖v p‖^2) ∂energyMeasure μ H)≤
      (∫⁻ s,k s ∂timeMeasure H)*M := by
    calc
      _ ≤ ∫⁻ p,k p.1*f p ∂energyMeasure μ H := lintegral_mono_ae h
      _ = ∫⁻ s,k s*(∫⁻ ω,f (s,ω) ∂μ) ∂timeMeasure H := by
        rw [energyMeasure,lintegral_prod _ hm.aemeasurable]
        apply lintegral_congr
        intro s
        have hsec : Measurable (fun ω => f (s,ω)) := hf.comp (measurable_const.prodMk measurable_id)
        exact lintegral_const_mul'' (k s) hsec.aemeasurable
      _ ≤ ∫⁻ s,k s*M ∂timeMeasure H :=
        lintegral_mono_ae (hM.mono fun s hs => mul_le_mul_right hs _)
      _ = _ := lintegral_mul_const'' _ hk.aemeasurable
  exact hfin.trans_lt (ENNReal.mul_lt_top hkm.lt_top hMtop.lt_top)

end SHEStochastic.ScalarLipschitzItoMoment
