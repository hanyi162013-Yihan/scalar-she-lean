module

public import SHE.FullHorizonTargetContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeGammaClock
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (v b : ℝ≥0)

def window : Set (ℝ≥0×Ω):={p|v<p.1 ∧ p.1<b}
def age (p : ℝ≥0×Ω) : ℝ:=by
  classical
  exact if p∈window v b then (b:ℝ)-(p.1:ℝ) else 1

theorem window_measurable : MeasurableSet[𝓕.predictable] (window (Ω:=Ω) v b):=by
  have ht:=PredictableClock.real_time_measurable 𝓕
  exact (measurableSet_lt measurable_const ht).inter (measurableSet_lt ht measurable_const)

theorem age_measurable : Measurable[𝓕.predictable] (age (Ω:=Ω) v b):=
  (measurable_const.sub (PredictableClock.real_time_measurable 𝓕)).ite
    (window_measurable 𝓕 v b) measurable_const

theorem age_pos (p : ℝ≥0×Ω) : 0<age v b p:=by
  classical
  unfold age
  split_ifs with h
  · exact sub_pos.mpr (by exact_mod_cast h.2)
  · norm_num

theorem age_le_one (hb1 : (b:ℝ)≤1) (p : ℝ≥0×Ω) : age v b p≤1:=by
  classical
  unfold age
  split_ifs
  · exact (sub_le_self _ p.1.coe_nonneg).trans hb1
  · exact le_rfl

include 𝓕 in
/-- Actual stopped native age has an integrable square-root singularity
on the ORIGINAL full-H energy measure, even when b is strictly earlier
than H. -/
theorem power_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (hbH : b≤H) (hb1 : (b:ℝ)≤1) {ρ : ℝ} (hρ : 0≤ρ) :
    Integrable ((window v b).indicator (fun p=>(age v b p)^(ρ-1/2))) (energyMeasure μ H) := by
  have hm:=FullHorizonTargetContinuity.majorant_integrable (M:=1) 𝓕 μ H b hbH
  have hi:=hm.const_mul (1/StoppedFourier.heatConstant)
  have hs : StronglyMeasurable ((window (Ω:=Ω) v b).indicator (fun p=>(age v b p)^(ρ-1/2))):=by
    exact (((age_measurable 𝓕 v b).pow_const _).indicator (window_measurable 𝓕 v b)).stronglyMeasurable.mono
      (predictable_le_product 𝓕)
  apply hi.mono' hs.aestronglyMeasurable
  filter_upwards with p
  by_cases hp : p∈window v b
  · rw [indicator_of_mem hp,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (age_pos v b p).le _)]
    have hb : p∈StoppedItoInputs.before (Ω:=Ω) (b:ℝ):=by exact_mod_cast hp.2
    rw [FullHorizonTargetContinuity.majorant,indicator_of_mem hb]
    have hh : (age v b p)^(ρ-1/2)≤(age v b p)^(-(1/2:ℝ)):=
      Real.rpow_le_rpow_of_exponent_ge (age_pos v b p) (age_le_one v b hb1 p) (by linarith)
    have he : age v b p=(b:ℝ)-(p.1:ℝ):=if_pos hp
    rw [he] at hh
    have hc:=StoppedFourier.heatConstant_pos
    have hd : (1/StoppedFourier.heatConstant)*(1*(1+StoppedFourier.heatConstant*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ))))=
      1/StoppedFourier.heatConstant+((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)):=by field_simp
    rw [hd,he]
    exact hh.trans (le_add_of_nonneg_left (one_div_nonneg.mpr hc.le))
  · rw [indicator_of_notMem hp,norm_zero]
    exact mul_nonneg (one_div_nonneg.mpr StoppedFourier.heatConstant_pos.le) (by
      unfold FullHorizonTargetContinuity.majorant
      apply Set.indicator_nonneg
      intro p hp
      exact mul_nonneg zero_le_one (add_nonneg zero_le_one (mul_nonneg StoppedFourier.heatConstant_pos.le
        (Real.rpow_nonneg (sub_nonneg.mpr (le_of_lt hp)) _))))

end SHE.NativeGammaClock
