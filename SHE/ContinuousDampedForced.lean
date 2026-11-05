module

public import SHE.DampedPredictableVersion
public import SHE.DampedIntegralCongruence
public import SHE.ContinuousHeatMild
public import SHE.DampedNonlinearConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ContinuousDampedForced
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand ContinuousHeatMild
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace StateL2 := borel StateL2
local instance : BorelSpace StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
variable {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
variable (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
variable (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)

/-- The constructed damped L² fixed point with actual continuous forcing
has a continuous predictable representative satisfying the literal
damped nonlinear mild equation at every fixed time. -/
theorem continuous_representative (hpos : 0 < h)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (F : ℝ≥0 → Ω → StateL2) (hFc : ∀ ω,Continuous (fun t => F t ω))
    (hFp : StronglyMeasurable[𝓕.predictable] (Function.uncurry F))
    (w : Process (E := StateL2) 𝓕 μ h) (hw : w =ᵐ[energyMeasure μ h] Function.uncurry F)
    (v : Process (E := StateL2) 𝓕 μ h)
    (hv : v=w+DampedNonlinearConvolution.map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I v) :
    ∃ U : ℝ≥0 → Ω → StateL2,
      (∀ ω,Continuous (fun t => U t ω)) ∧
      StronglyMeasurable[𝓕.predictable] (Function.uncurry U) ∧
      v =ᵐ[energyMeasure μ h] Function.uncurry U ∧
      ∃ hfield : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb U),
        ∀ (t : ℝ≥0) (ht : t ≤ h), U t =ᵐ[μ]
          (fun ω => F t ω+DampedFixedIntegral.value 𝓕 μ h hh hΛ hell
            (hell.le.trans ((hb 0).1.trans (hb 0).2))
            (coefficientFunction ha hell hb U) hfield I t ht ω) := by
  let f := NonlinearConvolution.field 𝓕 μ h ha hell hb v
  have hf : StronglyMeasurable[𝓕.predictable] f :=
    NonlinearConvolution.field_predictable 𝓕 μ h ha hell hb hβ hH hholder v
  have hM : 0 ≤ M := hell.le.trans ((hb 0).1.trans (hb 0).2)
  let Y := DampedContinuousVersion.version 𝓕 μ h hh hΛ hell hM f hf I
  let U : ℝ≥0 → Ω → StateL2 := fun t ω => F t ω+Y t ω
  have hcont : ∀ ω,Continuous (fun t => U t ω) := fun ω =>
    (hFc ω).add (DampedContinuousVersion.continuous_version 𝓕 μ h hh hΛ hell hM f hf I hpos ω)
  have hpred : StronglyMeasurable[𝓕.predictable] (Function.uncurry U) := hFp.add
    (DampedPredictableVersion.predictable_version 𝓕 μ h hh hΛ hell hM f hf I B hBDG hnull hpos)
  have hN : DampedNonlinearConvolution.map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I v =ᵐ[energyMeasure μ h]
      (fun p : ℝ≥0 × Ω => Y p.1 p.2) :=
    DampedPredictableVersion.convolution_ae_version 𝓕 μ h hh hΛ hell hM f hf I B hBDG hpos
  have hEq : v =ᵐ[energyMeasure μ h] Function.uncurry U := by
    have hadd := ae_eq_of_ae_eq_trim (Lp.coeFn_add w
      (DampedNonlinearConvolution.map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I v))
    rw [hv]
    filter_upwards [hadd,hw,hN] with p hp hforce hnoise
    rw [hp]
    change w p+DampedNonlinearConvolution.map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I v p=U p.1 p.2
    rw [hforce,hnoise]
    rfl
  have hg : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb U) :=
    ((coefficientField_measurable ha hell hb hβ hH hholder).comp hpred.measurable).stronglyMeasurable
  have hfg : f =ᵐ[energyMeasure μ h] coefficientFunction ha hell hb U := by
    filter_upwards [hEq] with p hp
    change coefficientField a ha ell M hell hb (v p)=coefficientField a ha ell M hell hb (U p.1 p.2)
    rw [hp]
    rfl
  refine ⟨U,hcont,hpred,hEq,hg,?_⟩
  intro t ht
  have hY := DampedContinuousVersion.version_ae_of_le 𝓕 μ h hh hΛ hell hM f hf I B hBDG hpos t ht
  have he := DampedFixedIntegral.terminal_value_congr 𝓕 μ h hh hΛ hell hM f
    (coefficientFunction ha hell hb U) hf hg I hfg t ht
  filter_upwards [hY] with ω hω
  change Y t ω=DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t ht ω at hω
  change F t ω+Y t ω= _
  rw [hω,he]

end SHE.ContinuousDampedForced
