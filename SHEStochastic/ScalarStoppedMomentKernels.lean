module

public import SHEStochastic.ScalarStoppedMomentProfiles
public import SHE.TimeMeasureRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedMomentKernels
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation
open ScalarStoppedMildMoment ScalarStoppedMomentProfiles
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "tm" => PredictableL2.timeMeasure

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω)) (N : ℕ)

def ageKernel (t s : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (((t : ℝ)-(s : ℝ))^(-(1/2 : ℝ)))

private theorem unit_le_power {r h : ℝ} (hr : 0<r) (hh : r≤h) :
    1≤h^(1/2 : ℝ)*r^(-(1/2 : ℝ)) := by
  rw [Real.rpow_neg hr.le,←div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hr _),one_mul]
  exact Real.rpow_le_rpow hr.le hh (by norm_num)

theorem trace_le {r h : ℝ} (hr : 0<r) (hh : r≤h) :
    ScalarStoppedHeatItoEnergy.traceEnvelope r≤
      (h^(1/2 : ℝ)+2*HeatTrace.fractionalGaussianIntegral 0)*r^(-(1/2 : ℝ)) := by
  have hp := unit_le_power hr hh
  have hd : (2*r)^(-(1/2 : ℝ))≤r^(-(1/2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr (by linarith) (by norm_num)
  have hc := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ)<1/2)).le
  unfold ScalarStoppedHeatItoEnergy.traceEnvelope
  rw [add_mul]
  exact add_le_add hp (mul_le_mul_of_nonneg_left hd (by positivity))

include hW hc in
theorem drift (L : ℝ≥0) (t : ℝ≥0) :
    (∫⁻ ω,ENNReal.ofReal ((t : ℝ)*
      ∫ s,2*(L : ℝ)^2*liveGrowth W N s ω ∂tm t) ∂μ) =
      ENNReal.ofReal ((t : ℝ)*(2*(L : ℝ)^2))*
        (∫⁻ s,growth μ W N s ∂tm t) := by
  let f (p : ℝ≥0×Ω) := liveGrowth W N p.1 p.2
  have hm : Measurable f := growth_measurable F W hW hc N
  have hn (p : ℝ≥0×Ω) : 0≤f p := by
    change 0≤liveGrowth W N p.1 p.2
    unfold liveGrowth
    split <;> positivity
  have hb (p : ℝ≥0×Ω) : ‖f p‖≤1+(N : ℝ)^2 := by
    rw [Real.norm_of_nonneg (hn p)]
    change liveGrowth W N p.1 p.2≤_
    unfold liveGrowth
    split
    · gcongr
      exact (ContinuousNormExit.before_bound W hc N p.1 p.2 ‹_›).le
    · positivity
  have hi (ω : Ω) : Integrable (fun s => f (s,ω)) (tm t) :=
    Integrable.of_bound
      (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable _
      (ae_of_all _ fun s => hb (s,ω))
  calc
    _ = ∫⁻ ω,ENNReal.ofReal ((t : ℝ)*(2*(L : ℝ)^2)) *
        (∫⁻ s,ENNReal.ofReal (f (s,ω)) ∂tm t) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [integral_const_mul,←mul_assoc,ENNReal.ofReal_mul (by positivity),
        ofReal_integral_eq_lintegral_ofReal (hi ω) (ae_of_all _ fun s => hn (s,ω))]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact (lintegral_lintegral_swap (μ := tm t) (ν := μ)
        (f := fun s ω => ENNReal.ofReal (f (s,ω))) hm.ennreal_ofReal.aemeasurable).symm

open Classical in
include hW hc in
theorem heat (H t : ℝ≥0) (ht : t≤H) (K : ℝ) (hK : 0≤K) :
    (∫⁻ p,ENNReal.ofReal (if p∈ScalarStoppedHeatFourierInput.before W N t then
      ScalarStoppedHeatItoEnergy.traceEnvelope ((t : ℝ)-(p.1 : ℝ))*K*
        (1+‖W p.1 p.2‖^2) else 0) ∂energyMeasure μ H) ≤
      ENNReal.ofReal (( (H : ℝ)^(1/2 : ℝ)+2*HeatTrace.fractionalGaussianIntegral 0)*K)*
        (∫⁻ s,ageKernel t s*growth μ W N s ∂tm t) := by
  classical
  let B := ((H : ℝ)^(1/2 : ℝ)+2*HeatTrace.fractionalGaussianIntegral 0)*K
  have hG := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ)<1/2)).le
  have hB : 0≤B := by dsimp [B]; positivity
  let f (p : ℝ≥0×Ω) := ENNReal.ofReal (liveGrowth W N p.1 p.2)
  have hf : Measurable f := (growth_measurable F W hW hc N).ennreal_ofReal
  have hk : Measurable (ageKernel t) := by
    unfold ageKernel
    fun_prop
  let J : Set ℝ≥0 := Ioc 0 t
  have hJ : MeasurableSet J := measurableSet_Ioc
  calc
    _ ≤ ∫⁻ p, J.indicator (fun s => ENNReal.ofReal B*ageKernel t s) p.1 * f p
        ∂energyMeasure μ H := by
      rw [energyMeasure]
      apply lintegral_mono_ae
      have hp : ∀ᵐ p ∂(tm H).prod μ,p.1∈Ioc 0 H :=
        (Measure.quasiMeasurePreserving_fst (μ := tm H) (ν := μ)).ae (timeMeasure_ae_mem H)
      filter_upwards [hp] with p hp
      by_cases hs : p∈ScalarStoppedHeatFourierInput.before W N t
      · have hj : p.1∈J := ⟨hp.1,hs.1.le⟩
        have hr : 0<(t : ℝ)-(p.1 : ℝ) := sub_pos.mpr hs.1
        have hrH : (t : ℝ)-(p.1 : ℝ)≤H :=
          (sub_le_self _ p.1.property).trans (by exact_mod_cast ht)
        rw [ite_eq_left hs,indicator_of_mem hj]
        dsimp only [f,ageKernel]
        have hexit : (p.1 : WithTop ℝ≥0) < ContinuousNormExit.exit W N p.2 := hs.2
        rw [liveGrowth,ite_eq_left hexit,←ENNReal.ofReal_mul hB,
          ←ENNReal.ofReal_mul (mul_nonneg hB (Real.rpow_nonneg hr.le _))]
        apply ENNReal.ofReal_le_ofReal
        have htr := mul_le_mul_of_nonneg_right (trace_le hr hrH) hK
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          _ ≤ _ := htr
          _ = _ := by dsimp [B]; ring
      · simp [hs]
    _ = ∫⁻ s, J.indicator (fun s => ENNReal.ofReal B*(ageKernel t s*growth μ W N s)) s
        ∂tm H := by
      have hm : Measurable (fun p : ℝ≥0×Ω =>
          J.indicator (fun s => ENNReal.ofReal B*ageKernel t s) p.1 * f p) :=
        (((measurable_const.mul hk).indicator hJ).comp measurable_fst).mul hf
      rw [energyMeasure,lintegral_prod _ hm.aemeasurable]
      apply lintegral_congr
      intro s
      by_cases hs : s∈J
      · simp only [indicator_of_mem hs]
        have hka : ageKernel t s ≠ ⊤ := ENNReal.ofReal_ne_top
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hka),mul_assoc]
        rfl
      · simp [indicator_of_notMem hs]
    _ = _ := by
      rw [lintegral_indicator hJ,timeMeasure_restrict ht,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end SHEStochastic.ScalarStoppedMomentKernels
