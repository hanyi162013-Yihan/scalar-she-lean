module

public import SHE.StoppedInputParameter
public import SHE.LpIntegralFubini
public import SHE.ExponentialStopMass
public import SHE.PredictableDamping

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.StoppedInputResolvent
open MeasureTheory Set Filter PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable (v : Process (E := C) 𝓕 μ h)
local instance stoppedInputResolvent_energyFinite : IsFiniteMeasure (energyMeasure μ h) := by
  unfold energyMeasure
  infer_instance

theorem stop_norm_le (s : ℝ) : ‖stop 𝓕 μ h s v‖≤‖v‖ :=
  Lp.norm_le_norm_of_ae_le (f := stop 𝓕 μ h s v) (g := v)
    (StoppedInputParameter.norm_le_ae 𝓕 μ h v s)

def family (Λ : ℝ) (t s : ℝ≥0) : Process (E := C) 𝓕 μ h :=
  Real.exp (-Λ*((t:ℝ)-(s:ℝ))) • stop 𝓕 μ h (s:ℝ) v

def rawFamily (Λ : ℝ) (t : ℝ≥0) (q : ℝ≥0×(ℝ≥0×Ω)) : C :=
  Real.exp (-Λ*((t:ℝ)-(q.1:ℝ))) • (before (q.1:ℝ)).indicator v q.2

theorem family_stronglyMeasurable (Λ : ℝ) (t : ℝ≥0) :
    StronglyMeasurable (family 𝓕 μ h v Λ t) :=
  (show StronglyMeasurable (fun s : ℝ≥0 => Real.exp (-Λ*((t:ℝ)-(s:ℝ)))) from
    (show Continuous (fun s : ℝ≥0 => Real.exp (-Λ*((t:ℝ)-(s:ℝ)))) by fun_prop).stronglyMeasurable).smul
      (StoppedInputParameter.stronglyMeasurable 𝓕 μ h v)

theorem family_integrable {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0) :
    Integrable (family 𝓕 μ h v Λ t) (timeMeasure t) := by
  apply (integrable_const ‖v‖).mono' (family_stronglyMeasurable 𝓕 μ h v Λ t).aestronglyMeasurable
  filter_upwards [timeMeasure_ae_mem t] with s hs
  rw [family,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-Λ*((t:ℝ)-(s:ℝ)))≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (sub_nonneg.mpr (by exact_mod_cast hs.2)))
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
    (by simpa only [one_mul] using stop_norm_le 𝓕 μ h v (s:ℝ))

theorem rawFamily_stronglyMeasurable (Λ : ℝ) (t : ℝ≥0) :
    @StronglyMeasurable (ℝ≥0×(ℝ≥0×Ω)) C _
      ((inferInstance : MeasurableSpace ℝ≥0).prod 𝓕.predictable) (rawFamily 𝓕 μ h v Λ t) := by
  letI : MeasurableSpace (ℝ≥0×Ω) := 𝓕.predictable
  have hset : MeasurableSet {q : ℝ≥0×(ℝ≥0×Ω) | (q.2.1:ℝ)<(q.1:ℝ)} :=
    measurableSet_lt ((PredictableClock.real_time_measurable 𝓕).comp measurable_snd)
      (measurable_coe_nnreal_real.comp measurable_fst)
  have hv := (Lp.stronglyMeasurable v).comp_measurable (measurable_snd : Measurable
    (Prod.snd : ℝ≥0×(ℝ≥0×Ω)→ℝ≥0×Ω))
  have hw : StronglyMeasurable (fun q : ℝ≥0×(ℝ≥0×Ω) => Real.exp (-Λ*((t:ℝ)-(q.1:ℝ)))) :=
    (Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.sub (measurable_coe_nnreal_real.comp measurable_fst)))).stronglyMeasurable
  exact hw.smul (hv.indicator hset)

theorem rawFamily_integrable {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0) :
    Integrable (rawFamily 𝓕 μ h v Λ t)
      (@Measure.prod ℝ≥0 (ℝ≥0×Ω) inferInstance 𝓕.predictable
        (timeMeasure t) ((energyMeasure μ h).trim (predictable_le_product 𝓕))) := by
  letI : MeasurableSpace (ℝ≥0×Ω) := 𝓕.predictable
  have hi := ((Lp.memLp v).integrable (by norm_num : (1:ENNReal)≤2)).norm.comp_snd (timeMeasure t)
  apply hi.mono' (rawFamily_stronglyMeasurable 𝓕 μ h v Λ t).aestronglyMeasurable
  have hs := (Measure.quasiMeasurePreserving_fst (μ := timeMeasure t)
    (ν := (energyMeasure μ h).trim (predictable_le_product 𝓕))).ae (timeMeasure_ae_mem t)
  filter_upwards [hs] with q hq
  rw [rawFamily,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-Λ*((t:ℝ)-(q.1:ℝ)))≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (sub_nonneg.mpr (by exact_mod_cast hq.2)))
  apply (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
  rw [one_mul]
  exact norm_indicator_le_norm_self _ _

theorem family_rep (Λ : ℝ) (t s : ℝ≥0) :
    family 𝓕 μ h v Λ t s=ᵐ[(energyMeasure μ h).trim (predictable_le_product 𝓕)]
      fun p => rawFamily 𝓕 μ h v Λ t (s,p) := by
  filter_upwards [Lp.coeFn_smul (Real.exp (-Λ*((t:ℝ)-(s:ℝ)))) (stop 𝓕 μ h s v),
    StoppedInputParameter.stop_ae_trim 𝓕 μ h v s] with p hs hp
  change family 𝓕 μ h v Λ t s p=_
  rw [family,hs]
  change Real.exp (-Λ*((t:ℝ)-(s:ℝ))) • stop 𝓕 μ h s v p=_
  rw [hp]
  rfl

theorem integral_family_ae {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0) :
    (∫ s,family 𝓕 μ h v Λ t s ∂timeMeasure t)=ᵐ[(energyMeasure μ h).trim (predictable_le_product 𝓕)]
      fun p => ∫ s,rawFamily 𝓕 μ h v Λ t (s,p) ∂timeMeasure t := by
  letI : MeasurableSpace (ℝ≥0×Ω) := 𝓕.predictable
  exact LpIntegralFubini.integral_ae ((energyMeasure μ h).trim (predictable_le_product 𝓕))
    (timeMeasure t) _ (family_integrable 𝓕 μ h v hΛ t) _ (rawFamily_integrable 𝓕 μ h v hΛ t)
    (Eventually.of_forall (fun s => family_rep 𝓕 μ h v Λ t s))

theorem integral_rawFamily (Λ : ℝ) (t : ℝ≥0) (p : ℝ≥0×Ω) :
    (∫ s,rawFamily 𝓕 μ h v Λ t (s,p) ∂timeMeasure t)=ExponentialStopMass.mass Λ t p.1 • v p := by
  rw [ExponentialStopMass.mass,← integral_smul_const]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : p.1<s
  · rw [if_pos hs]
    exact congrArg (fun z : C => Real.exp (-Λ*((t:ℝ)-(s:ℝ))) • z)
      (Set.indicator_of_mem (show p∈before (Ω := Ω) (s:ℝ) from hs) v)
  · rw [if_neg hs,zero_smul]
    rw [rawFamily,Set.indicator_of_notMem (show p∉before (Ω := Ω) (s:ℝ) from hs),smul_zero]

end SHE.StoppedInputResolvent
