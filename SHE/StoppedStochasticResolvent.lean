module

public import SHE.StoppedResolventIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.StoppedStochasticResolvent
open MeasureTheory Set Filter PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable (v : Process (E := C) 𝓕 μ h)
variable (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)

def weighted (Λ : ℝ) (t : ℝ≥0) (Y : ℝ≥0×Ω→E) (p : ℝ≥0×Ω) : E :=
  Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) • Y p

theorem weighted_integrable {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0)
    {Y : ℝ≥0×Ω→E} (hY : Integrable Y ((timeMeasure t).prod μ)) :
    Integrable (weighted Λ t Y) ((timeMeasure t).prod μ) := by
  have hw : StronglyMeasurable (fun p : ℝ≥0×Ω => Real.exp (-Λ*((t:ℝ)-(p.1:ℝ)))) :=
    (Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.sub (measurable_coe_nnreal_real.comp measurable_fst)))).stronglyMeasurable
  apply hY.norm.mono' (hw.aestronglyMeasurable.smul hY.aestronglyMeasurable)
  have hs := (Measure.quasiMeasurePreserving_fst (μ := timeMeasure t) (ν := μ)).ae (timeMeasure_ae_mem t)
  filter_upwards [hs] with p hp
  change ‖Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) • Y p‖≤‖Y p‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-Λ*((t:ℝ)-(p.1:ℝ)))≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ)
      (sub_nonneg.mpr (by exact_mod_cast hp.2)))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg (Y p))

/-- Pointwise stochastic Volterra resolvent for an actual jointly
integrable version of the stopped integrals. Every term uses the same
terminal Itô map on the full horizon. The proof derives stochastic
Fubini from that map's linear isometry and ordinary Bochner Fubini. -/
theorem resolvent_ae {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0)
    (Y : ℝ≥0×Ω→E) (hY : Integrable Y ((timeMeasure t).prod μ))
    (hRep : ∀ᵐ (s : ℝ≥0) ∂timeMeasure t,I.integral (stop 𝓕 μ h (s:ℝ) v)=ᵐ[μ] fun ω => Y (s,ω)) :
    (fun ω => Λ • (∫ s,Real.exp (-Λ*((t:ℝ)-(s:ℝ))) • Y (s,ω) ∂timeMeasure t))=ᵐ[μ]
      fun ω => I.integral (stop 𝓕 μ h (t:ℝ) v) ω-
        I.integral (StoppedInputResolvent.damped 𝓕 μ h v hΛ t) ω := by
  have hfamily : ∀ᵐ s ∂timeMeasure t,
      I.integral (StoppedInputResolvent.family 𝓕 μ h v Λ t s)=ᵐ[μ]
        fun ω => weighted Λ t Y (s,ω) := by
    filter_upwards [hRep] with s hs
    rw [StoppedInputResolvent.family,map_smul]
    filter_upwards [Lp.coeFn_smul (Real.exp (-Λ*((t:ℝ)-(s:ℝ))))
      (I.integral (stop 𝓕 μ h (s:ℝ) v)),hs] with ω hc hr
    rw [hc]
    change Real.exp (-Λ*((t:ℝ)-(s:ℝ))) • I.integral (stop 𝓕 μ h (s:ℝ) v) ω=_
    rw [hr]
    rfl
  have hi := TerminalItoFubini.integral_ae 𝓕 μ h I (timeMeasure t)
    (StoppedInputResolvent.family 𝓕 μ h v Λ t)
    (StoppedInputResolvent.family_integrable 𝓕 μ h v hΛ t)
    (weighted Λ t Y) (weighted_integrable μ hΛ t hY) hfamily
  have he := StoppedInputResolvent.integral_resolvent 𝓕 μ h v I hΛ t
  rw [← TerminalItoFubini.integral_comm] at he
  filter_upwards [hi,Lp.coeFn_smul Λ
    (I.integral (∫ s,StoppedInputResolvent.family 𝓕 μ h v Λ t s ∂timeMeasure t)),
    Lp.coeFn_sub (I.integral (stop 𝓕 μ h (t:ℝ) v))
      (I.integral (StoppedInputResolvent.damped 𝓕 μ h v hΛ t))] with ω hiω hsm hsub
  have hp := congrArg (fun z : Lp E 2 μ => z ω) he
  rw [hsm,hsub] at hp
  change Λ • (I.integral (∫ s,StoppedInputResolvent.family 𝓕 μ h v Λ t s ∂timeMeasure t)) ω=_ at hp
  rw [hiω] at hp
  exact hp

end SHE.StoppedStochasticResolvent
