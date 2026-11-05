module

public import SHE.HaarPredictableVersion
public import SHE.HaarIntegralCongruence
public import SHE.ConstructedPicard

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ContinuousHeatMild
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand
open scoped NNReal ENNReal
local instance continuousHeatMild_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance continuousHeatMild_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance continuousHeatMild_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance continuousHeatMild_stateSigma : MeasurableSpace StateL2 := borel StateL2
local instance continuousHeatMild_stateBorel : BorelSpace StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
variable (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
variable (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)

def coefficientFunction (U : ℝ≥0 → Ω → StateL2) : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M :=
  fun p => coefficientField a ha ell M hell hb (U p.1 p.2)

/-- Every constructed heat-initial L² Picard solution has an actual
continuous predictable representative which solves the literal nonlinear
stochastic heat equation at every fixed time. Its coefficient is evaluated
at that continuous representative itself. -/
theorem continuous_representative (hpos : 0 < h)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) (u₀ : StateL2)
    (v : Process (E := StateL2) 𝓕 μ h)
    (hv : v=HeatInitialProcess.process 𝓕 μ h u₀+
      NonlinearConvolution.map 𝓕 μ h ha hell hb hβ hH hholder I v) :
    ∃ U : ℝ≥0 → Ω → StateL2,
      (∀ ω,Continuous (fun t => U t ω)) ∧
      StronglyMeasurable[𝓕.predictable] (Function.uncurry U) ∧
      v =ᵐ[energyMeasure μ h] Function.uncurry U ∧
      ∃ hfield : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb U),
        ∀ (t : ℝ≥0) (ht : t ≤ h), U t =ᵐ[μ]
          (fun ω => RealHeat.realHeat (t:ℝ) u₀+
            TerminalHaarConvolution.value 𝓕 μ h hh hell
              (hell.le.trans ((hb 0).1.trans (hb 0).2))
              (coefficientFunction ha hell hb U) hfield I t ht ω) := by
  let f := NonlinearConvolution.field 𝓕 μ h ha hell hb v
  have hf : StronglyMeasurable[𝓕.predictable] f :=
    NonlinearConvolution.field_predictable 𝓕 μ h ha hell hb hβ hH hholder v
  have hM : 0 ≤ M := hell.le.trans ((hb 0).1.trans (hb 0).2)
  let Y := HaarContinuousVersion.version 𝓕 μ h hh hell hM f hf I
  let U : ℝ≥0 → Ω → StateL2 := fun t ω => RealHeat.realHeat (t:ℝ) u₀+Y t ω
  have hcont : ∀ ω,Continuous (fun t => U t ω) := by
    intro ω
    have ht : Continuous (fun t : ℝ≥0 => (t:ℝ)) := continuous_subtype_val
    have hp : Continuous (fun t : ℝ≥0 => ((t:ℝ),u₀)) := ht.prodMk continuous_const
    have hc := RealHeat.continuous_realHeat_action.comp hp
    change Continuous (fun t : ℝ≥0 => RealHeat.realHeat (t:ℝ) u₀) at hc
    exact hc.add (HaarContinuousVersion.continuous_version 𝓕 μ h hh hell hM f hf I hpos ω)
  have hpred : StronglyMeasurable[𝓕.predictable] (Function.uncurry U) :=
    (HeatInitialProcess.predictable 𝓕 u₀).add
      (HaarPredictableVersion.predictable_version 𝓕 μ h hh hell hM f hf I B hBDG hnull hpos)
  have hN : NonlinearConvolution.map 𝓕 μ h ha hell hb hβ hH hholder I v =ᵐ[energyMeasure μ h]
      (fun p : ℝ≥0 × Ω => Y p.1 p.2) :=
    HaarPredictableVersion.convolution_ae_version 𝓕 μ h hh hell hM f hf I B hBDG hpos
  have hEq : v =ᵐ[energyMeasure μ h] Function.uncurry U := by
    have hadd := ae_eq_of_ae_eq_trim (Lp.coeFn_add (HeatInitialProcess.process 𝓕 μ h u₀)
      (NonlinearConvolution.map 𝓕 μ h ha hell hb hβ hH hholder I v))
    rw [hv]
    filter_upwards [hadd,HeatInitialProcess.process_ae 𝓕 μ h u₀,hN] with p hp hheat hnoise
    rw [hp]
    change HeatInitialProcess.process 𝓕 μ h u₀ p+
      NonlinearConvolution.map 𝓕 μ h ha hell hb hβ hH hholder I v p=U p.1 p.2
    rw [hheat,hnoise]
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
  have hY := HaarContinuousVersion.version_ae_of_le 𝓕 μ h hh hell hM f hf I B hBDG hpos t ht
  have he := FixedHaarIntegral.terminal_value_congr 𝓕 μ h hh hell hM f
    (coefficientFunction ha hell hb U) hf hg I hfg t ht
  filter_upwards [hY] with ω hω
  change Y t ω=TerminalHaarConvolution.value 𝓕 μ h hh hell hM f hf I t ht ω at hω
  change RealHeat.realHeat (t:ℝ) u₀+Y t ω= _
  rw [hω,he]

include hβ hH hholder in
/-- The proved short-time Picard theorem therefore constructs a genuine
continuous predictable mild solution, using only terminal Hilbert Ito and
BDG among the accepted stochastic inputs. -/
theorem exists_continuous_heat_mild (hpos : 0 < h)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (u₀ : StateL2) :
    ∃ U : ℝ≥0 → Ω → StateL2,
      (∀ ω,Continuous (fun t => U t ω)) ∧
      StronglyMeasurable[𝓕.predictable] (Function.uncurry U) ∧
      ∃ hfield : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb U),
        ∀ (t : ℝ≥0) (ht : t ≤ h), U t =ᵐ[μ]
          (fun ω => RealHeat.realHeat (t:ℝ) u₀+
            TerminalHaarConvolution.value 𝓕 μ h hh hell
              (hell.le.trans ((hb 0).1.trans (hb 0).2))
              (coefficientFunction ha hell hb U) hfield I t ht ω) := by
  obtain ⟨v,hv,_⟩ := ConstructedPicard.exists_unique_heat_mild 𝓕 μ h ha hell hb hβ hH hholder
    hLip hh hsmall I u₀
  obtain ⟨U,hc,hp,_,hf,hmild⟩ := continuous_representative 𝓕 μ h hh ha hell hb hβ hH hholder
    I hpos hnull B hBDG u₀ v hv
  exact ⟨U,hc,hp,hf,hmild⟩

end SHE.ContinuousHeatMild
