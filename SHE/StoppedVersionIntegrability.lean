module

public import SHE.StoppedStochasticResolvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHE.StoppedStochasticResolvent
open MeasureTheory Filter PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable (v : Process (E := C) 𝓕 μ h)
variable (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)

/-- Joint measurability of a stopped-integral version already supplies
the integrability needed for the pointwise resolvent: the fixed-horizon
Itô isometry and the stopped-row contraction provide a uniform L¹ bound. -/
theorem version_integrable (t : ℝ≥0) (Y : ℝ≥0×Ω→E)
    (hY : AEStronglyMeasurable Y ((timeMeasure t).prod μ))
    (hRep : ∀ᵐ (s : ℝ≥0) ∂timeMeasure t,I.integral (stop 𝓕 μ h (s:ℝ) v)=ᵐ[μ] fun ω => Y (s,ω)) :
    Integrable Y ((timeMeasure t).prod μ) := by
  apply (integrable_prod_iff hY).mpr
  constructor
  · filter_upwards [hRep] with s hs
    exact ((Lp.memLp (I.integral (stop 𝓕 μ h (s:ℝ) v))).integrable
      (by norm_num : (1:ENNReal)≤2)).congr hs
  · apply (integrable_const ‖v‖).mono' hY.norm.integral_prod_right'
    filter_upwards [hRep] with s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have he : (∫ x,‖Y (s,x)‖ ∂μ)=∫ x,‖I.integral (stop 𝓕 μ h (s:ℝ) v) x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hs] with x hx
      exact congrArg norm hx.symm
    rw [he]
    have hb := LpIntegralFubini.integral_norm_le_norm μ (I.integral (stop 𝓕 μ h (s:ℝ) v))
    have hm : μ.real Set.univ=1 := by simp [Measure.real]
    simp only [hm,Real.sqrt_one,one_mul,LinearIsometry.norm_map] at hb
    exact hb.trans (StoppedInputResolvent.stop_norm_le 𝓕 μ h v (s:ℝ))

theorem resolvent_ae_of_measurable {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0)
    (Y : ℝ≥0×Ω→E) (hY : AEStronglyMeasurable Y ((timeMeasure t).prod μ))
    (hRep : ∀ᵐ (s : ℝ≥0) ∂timeMeasure t,I.integral (stop 𝓕 μ h (s:ℝ) v)=ᵐ[μ] fun ω => Y (s,ω)) :
    (fun ω => Λ • (∫ s,Real.exp (-Λ*((t:ℝ)-(s:ℝ))) • Y (s,ω) ∂timeMeasure t))=ᵐ[μ]
      fun ω => I.integral (stop 𝓕 μ h (t:ℝ) v) ω-
        I.integral (StoppedInputResolvent.damped 𝓕 μ h v hΛ t) ω :=
  resolvent_ae 𝓕 μ h v I hΛ t Y (version_integrable 𝓕 μ h v I t Y hY hRep) hRep

end SHE.StoppedStochasticResolvent
