module

public import SHEStochastic.ScalarStoppedMildVolterra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedMomentUniform
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open ScalarStoppedMildMoment ScalarStoppedMomentProfiles ScalarStoppedMildVolterra
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local notation "tm" => PredictableL2.timeMeasure

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (J : StandardTerminalIto (C := Noise) (E := ℝ) F μ H)
  (b : ScalarLinearGrowthDriftField.Data H) (a : ℝ≥0 → Ω → ℝ)
  (u₀ : RealL2)

local notation "K" => (4*(‖g 0‖+(C : ℝ))^2)
local notation "A" => (1+3*‖u₀‖^2)
local notation "B" => (3*(driftWeight H b.growth+heatWeight H K))

include hc in
private theorem live_mono : Monotone (fun N (p : ℝ≥0×Ω) =>
    ENNReal.ofReal (liveNormSq W N p.1 p.2)) := by
  intro N M hNM p
  by_cases hN : (p.1 : WithTop ℝ≥0)<ContinuousNormExit.exit W N p.2
  · have hM := hN.trans_le (ContinuousNormExit.monotone W hc p.2 hNM)
    simp only [liveNormSq,ite_eq_left hN,ite_eq_left hM,le_refl]
  · simp only [liveNormSq,ite_eq_right hN,ENNReal.ofReal_zero,zero_le]

/-- Full integrated second moment with a deterministic bound uniform
over equivalent stopped laws and all drift multipliers in the unit interval. -/
theorem bound :
    ∃ R : ℝ,0≤R ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
        (hc : ∀ ω,Continuous (fun t => W t ω))
        (J : StandardTerminalIto (C := Noise) (E := ℝ) F μ H)
        (a : ℝ≥0 → Ω → ℝ),
        Equation F μ H W hW hc hg hβ hβ₁ J b a u₀ →
        (∀ ω,Measurable (fun s => a s ω)) → (∀ s ω,|a s ω|≤1) →
        (∫⁻ p,ENNReal.ofReal (‖W p.1 p.2‖^2) ∂energyMeasure μ H)≤ENNReal.ofReal R := by
  have hGaussian := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ)<1/2)).le
  have hB : 0≤B := by unfold driftWeight heatWeight; positivity
  obtain ⟨R,hR,hbound⟩ := ScalarMomentBielecki.bound H A B (by positivity) hB
  refine ⟨R,hR,?_⟩
  intro Ω _ F μ _ W hW hc J a heq ham ha
  let f (N : ℕ) (p : ℝ≥0×Ω) := ENNReal.ofReal (liveNormSq W N p.1 p.2)
  have hf (N : ℕ) : Measurable (f N) := (norm_measurable F W hW hc N).ennreal_ofReal
  have hb (N : ℕ) : (∫⁻ p,f N p ∂energyMeasure μ H)≤ENNReal.ofReal R := by
    rw [energyMeasure,lintegral_prod _ (hf N).aemeasurable]
    change (∫⁻ t,second μ W N t ∂tm H)≤_
    have hle (t : ℝ≥0) : second μ W N t≤1+second μ W N t := le_add_self
    refine (lintegral_mono hle).trans ?_
    apply hbound (fun t => 1+second μ W N t) (1+(N : ℝ≥0)^2)
    · exact measurable_const.add (second_measurable F μ W hW hc N)
    · intro t
      push_cast
      exact add_le_add_right (second_le μ W hc N t) _
    · filter_upwards [timeMeasure_ae_mem H] with t ht
      exact profile F μ H W hW hc hg hβ hβ₁ J b a u₀ heq ham ha N t ht.2
  have he : (fun p : ℝ≥0×Ω => ENNReal.ofReal (‖W p.1 p.2‖^2)) = fun p => ⨆ N,f N p := by
    funext p
    exact full_eq_iSup W p.1 p.2 hc
  rw [he,lintegral_iSup hf (live_mono W hc)]
  exact iSup_le hb

include hW in
omit [IsProbabilityMeasure μ] in
/-- A finite integrated second moment gives the exact growth-integrability
hypothesis required to build the original predictable b/g control. -/
theorem integrable_sq
    (h : (∫⁻ p,ENNReal.ofReal (‖W p.1 p.2‖^2) ∂energyMeasure μ H)<⊤) :
    Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H) := by
  refine ⟨((hW.mono (predictable_le_product F)).norm.pow 2).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)]
  exact h

end SHEStochastic.ScalarStoppedMomentUniform
