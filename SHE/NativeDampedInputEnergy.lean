module
public import SHE.NativeDampedHaarInput
public import SHE.NativeBieleckiColumnEnergy
public import SHE.StandardTerminalIto
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeDampedInputEnergy
open MeasureTheory Set PredictableL2 FiniteHaar LowBands
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
variable (f g : ℝ≥0 × Ω → EllipticField ell M)
variable (hf : StronglyMeasurable[𝓕.predictable] f) (hg : StronglyMeasurable[𝓕.predictable] g)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ H)

private theorem lp_difference_energy (U V : Lp StateL2 2 μ) :
    ENNReal.ofReal (‖U-V‖^2) = ∫⁻ω, ENNReal.ofReal (‖U ω-V ω‖^2) ∂μ := by
  rw [realLp_norm_sq, ofReal_integral_eq_lintegral_ofReal
    (Lp.memLp (U-V)).norm.integrable_sq (ae_of_all _ (fun _ => sq_nonneg _))]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub U V] with ω hω
  rw [hω]
  rfl

/-- Exact terminal energy for the literal native damped Haar inputs,
under the SAME Hilbert integral on the original full horizon. -/
theorem fixed (t : ℝ≥0) (ht : t ≤ H) (ht1 : (t:ℝ) ≤ 1) :
    (∫⁻ω, ENNReal.ofReal (‖I.integral
      (NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM f hf t ht ht1) ω -
      I.integral (NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM g hg t ht ht1) ω‖^2) ∂μ) =
    ∫⁻s, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ))) *
      ‖NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω)) -
        NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),g (s,ω))‖^2)
      ∂μ ∂timeMeasure t := by
  let uf := NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM f hf t ht ht1
  let ug := NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM g hg t ht ht1
  have he := I.difference_energy uf ug
  rw [lp_difference_energy μ] at he
  change (∫⁻ω, ENNReal.ofReal (‖I.integral uf ω-I.integral ug ω‖^2) ∂μ) = _
  calc
    _ = ∫⁻s, ∫⁻ω, ENNReal.ofReal (‖uf (s,ω)-ug (s,ω)‖^2) ∂μ ∂timeMeasure H := he
    _ = ∫⁻s, ∫⁻ω, ENNReal.ofReal
      (‖NativeDampedHaarInput.raw (Λ:=Λ) hell f t (s,ω) -
        NativeDampedHaarInput.raw (Λ:=Λ) hell g t (s,ω)‖^2) ∂μ ∂timeMeasure H := by
      have hae := Measure.ae_ae_of_ae_prod
        ((NativeDampedHaarInput.input_ae 𝓕 μ H hΛ hell hM f hf t ht ht1).prodMk
          (NativeDampedHaarInput.input_ae 𝓕 μ H hΛ hell hM g hg t ht ht1))
      apply lintegral_congr_ae
      filter_upwards [hae] with s hs
      apply lintegral_congr_ae
      filter_upwards [hs] with ω hω
      have hω := Prod.mk.inj hω
      rw [hω.1,hω.2]
    _ = ∫⁻s, ∫⁻ω, ENNReal.ofReal
      (‖NativeDampedHaarInput.raw (Λ:=Λ) hell f t (s,ω) -
        NativeDampedHaarInput.raw (Λ:=Λ) hell g t (s,ω)‖^2) ∂μ ∂timeMeasure t := by
      rw [← timeMeasure_restrict ht, ← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr_ae
      filter_upwards [timeMeasure_ae_mem H] with s hs
      by_cases hst : s ≤ t
      · rw [Set.indicator_of_mem (show s ∈ Ioc 0 t from ⟨hs.1,hst⟩)]
      · rw [Set.indicator_of_notMem (show s ∉ Ioc 0 t from fun hh => hst hh.2)]
        have hτ : (t:ℝ)-(s:ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hst))
        simp only [NativeDampedHaarInput.raw,NativeFixedHaarInput.raw,
          NativeHeatObservation.kernel_zero hell hτ,smul_zero,sub_self,norm_zero,
          zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero,lintegral_zero]
    _ = _ := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro ω
      congr 1
      rw [NativeDampedHaarInput.raw,NativeDampedHaarInput.raw,
        NativeFixedHaarInput.raw,NativeFixedHaarInput.raw,← smul_sub,norm_smul,
        Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
      have hexp : Real.exp (-Λ*((t:ℝ)-(s:ℝ)))^2 =
          Real.exp (-2*Λ*((t:ℝ)-(s:ℝ))) := by
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      rw [hexp]
end SHE.NativeDampedInputEnergy
