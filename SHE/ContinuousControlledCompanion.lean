module

public import SHE.ContinuousDampedForced
public import SHE.ControlledForcing

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ContinuousControlledCompanion
open MeasureTheory Set Filter PredictableL2 LowBands ContinuousHeatMild
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace StateL2 := borel StateL2
local instance : BorelSpace StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
variable (U : ℝ≥0 → Ω → StateL2)
variable (haU : StronglyAdapted 𝓕 U) (hcU : ∀ ω,Continuous (fun t => U t ω))
variable (u : Process (E := StateL2) 𝓕 μ h)
variable (hu : u =ᵐ[energyMeasure μ h] Function.uncurry U)

def force (u₀ : StateL2) (t : ℝ≥0) (ω : Ω) : StateL2 :=
  Real.exp (-Λ*(t:ℝ)) • RealHeat.realHeat (t:ℝ) u₀+
    Λ • VolterraPath.value Λ (fun s => U s ω) t

include hcU in
theorem continuous_force (u₀ : StateL2) (ω : Ω) :
    Continuous (fun t => force (Λ := Λ) U u₀ t ω) := by
  have hp : Continuous (fun t : ℝ≥0 => ((t:ℝ),u₀)) := continuous_subtype_val.prodMk continuous_const
  have hc := RealHeat.continuous_realHeat_action.comp hp
  change Continuous (fun t : ℝ≥0 => RealHeat.realHeat (t:ℝ) u₀) at hc
  exact ((by fun_prop : Continuous (fun t : ℝ≥0 => Real.exp (-Λ*(t:ℝ)))).smul hc).add
    ((VolterraPath.continuous_value Λ (hcU ω)).const_smul Λ)

include haU hcU in
theorem predictable_force (u₀ : StateL2) :
    StronglyMeasurable[𝓕.predictable] (Function.uncurry (force (Λ := Λ) U u₀)) :=
  (ControlledForcing.initial_predictable 𝓕 (Λ := Λ) u₀).add
    ((VolterraPredictable.value_predictable 𝓕 Λ U haU hcU).const_smul Λ)

include haU hcU hu in
/-- The actual controlled companion is constructed, including its
continuous predictable paths, finite energy and literal damped mild
equation. The driving terminal Hilbert integral is the prescribed one.
The input U may be arbitrary continuous adapted finite-energy data. -/
theorem exists_continuous_companion {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
    (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
    (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (hpos : 0 < h) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) (u₀ : StateL2) :
    ∃ (v : Process (E := StateL2) 𝓕 μ h) (V : ℝ≥0 → Ω → StateL2),
      (∀ ω,Continuous (fun t => V t ω)) ∧
      StronglyMeasurable[𝓕.predictable] (Function.uncurry V) ∧
      v =ᵐ[energyMeasure μ h] Function.uncurry V ∧
      ∃ hfield : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb V),
        ∀ (t : ℝ≥0) (ht : t ≤ h), V t =ᵐ[μ]
          (fun ω => Real.exp (-Λ*(t:ℝ)) • RealHeat.realHeat (t:ℝ) u₀+
            Λ • VolterraPath.value Λ (fun s => U s ω) t+
            DampedFixedIntegral.value 𝓕 μ h hh hΛ hell
              (hell.le.trans ((hb 0).1.trans (hb 0).2))
              (coefficientFunction ha hell hb V) hfield I t ht ω) := by
  obtain ⟨v,hv,_⟩ := ControlledForcing.exists_unique_controlled 𝓕 μ h hΛ U haU hcU u hu
    ha hell hb hβ hH hholder hLip hh hsmall I u₀
  have hw : ControlledForcing.forcing 𝓕 μ h hΛ U haU hcU u hu u₀ =ᵐ[energyMeasure μ h]
      Function.uncurry (force (Λ := Λ) U u₀) := ControlledForcing.forcing_ae 𝓕 μ h hΛ U haU hcU u hu u₀
  obtain ⟨V,hc,hp,he,hf,hmild⟩ := ContinuousDampedForced.continuous_representative
    𝓕 μ h hh hΛ ha hell hb hβ hH hholder I hpos hnull B hBDG
    (force (Λ := Λ) U u₀) (continuous_force U hcU u₀) (predictable_force 𝓕 U haU hcU u₀)
    (ControlledForcing.forcing 𝓕 μ h hΛ U haU hcU u hu u₀) hw v hv
  exact ⟨v,V,hc,hp,he,hf,hmild⟩

end SHE.ContinuousControlledCompanion
