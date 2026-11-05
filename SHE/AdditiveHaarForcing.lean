module

public import SHE.ContinuousDampedForced

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.AdditiveHaarForcing
open MeasureTheory Set Filter PredictableL2 LowBands FiniteHaar NonlinearHaarIntegrand ContinuousHeatMild
open scoped NNReal ENNReal
local instance additiveHaarForcing_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance additiveHaarForcing_stateSigma : MeasurableSpace StateL2 := borel _
local instance additiveHaarForcing_stateBorel : BorelSpace StateL2 := ⟨rfl⟩

def constantField (κ : ℝ) (hκ : 0 < κ) : EllipticField κ κ :=
  coefficientField (fun _ => κ) measurable_const κ κ hκ (fun _ => ⟨le_rfl,le_rfl⟩) 0

theorem constantField_ae (κ : ℝ) (hκ : 0 < κ) :
    (constantField κ hκ).1=ᵐ[AddCircle.haarAddCircle] (fun _ => (κ:ℂ)) :=
  CoefficientFields.coefficient_ae _ _ _ _ 0

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
variable (κ : ℝ) (hκ : 0 < κ)
variable (I₀ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)

def noiseProcess : Process (E := StateL2) 𝓕 μ h :=
  DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hκ hκ.le I₀
    (fun _ => constantField κ hκ) stronglyMeasurable_const

def noiseVersion (t : ℝ≥0) (ω : Ω) : StateL2 :=
  DampedContinuousVersion.version 𝓕 μ h hh hΛ hκ hκ.le
    (fun _ => constantField κ hκ) stronglyMeasurable_const I₀ t ω

theorem noiseVersion_continuous (hpos : 0 < h) (ω : Ω) :
    Continuous (fun t => noiseVersion 𝓕 μ h hh hΛ κ hκ I₀ t ω) :=
  DampedContinuousVersion.continuous_version 𝓕 μ h hh hΛ hκ hκ.le
    (fun _ => constantField κ hκ) stronglyMeasurable_const I₀ hpos ω

theorem noiseVersion_predictable (hpos : 0 < h)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I₀ B) :
    StronglyMeasurable[𝓕.predictable] (Function.uncurry (noiseVersion 𝓕 μ h hh hΛ κ hκ I₀)) :=
  DampedPredictableVersion.predictable_version 𝓕 μ h hh hΛ hκ hκ.le
    (fun _ => constantField κ hκ) stronglyMeasurable_const I₀ B hBDG hnull hpos

theorem noiseProcess_ae (hpos : 0 < h) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I₀ B) :
    noiseProcess 𝓕 μ h hh hΛ κ hκ I₀=ᵐ[energyMeasure μ h]
      Function.uncurry (noiseVersion 𝓕 μ h hh hΛ κ hκ I₀) :=
  DampedPredictableVersion.convolution_ae_version 𝓕 μ h hh hΛ hκ hκ.le
    (fun _ => constantField κ hκ) stronglyMeasurable_const I₀ B hBDG hpos

theorem noiseVersion_ae (hpos : 0 < h) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I₀ B)
    (t : ℝ≥0) (ht : t ≤ h) :
    noiseVersion 𝓕 μ h hh hΛ κ hκ I₀ t=ᵐ[μ]
      DampedFixedIntegral.value 𝓕 μ h hh hΛ hκ hκ.le
        (fun _ => constantField κ hκ) stronglyMeasurable_const I₀ t ht :=
  DampedContinuousVersion.version_ae_of_le 𝓕 μ h hh hΛ hκ hκ.le
    (fun _ => constantField κ hκ) stronglyMeasurable_const I₀ B hBDG hpos t ht

/-- A genuine continuous predictable solution with separate additive
and residual common-Haar noises. The additive convolution is constructed
as part of the forcing; no supplied nonlinear convolution map is used. -/
theorem exists_forced {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
    (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
    (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (hpos : 0 < h) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B₀ B₁ : ℝ≥0) (hBDG₀ : StandardTerminalBDG16 I₀ B₀) (hBDG₁ : StandardTerminalBDG16 I₁ B₁)
    (F : ℝ≥0 → Ω → StateL2) (hFc : ∀ ω,Continuous (fun t => F t ω))
    (hFp : StronglyMeasurable[𝓕.predictable] (Function.uncurry F))
    (w : Process (E := StateL2) 𝓕 μ h) (hw : w=ᵐ[energyMeasure μ h] Function.uncurry F) :
    ∃ (v : Process (E := StateL2) 𝓕 μ h) (V : ℝ≥0 → Ω → StateL2),
      (∀ ω,Continuous (fun t => V t ω)) ∧
      StronglyMeasurable[𝓕.predictable] (Function.uncurry V) ∧
      v=ᵐ[energyMeasure μ h] Function.uncurry V ∧
      ∃ hfield : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb V),
        ∀ (t : ℝ≥0) (ht : t ≤ h),V t=ᵐ[μ]
          (fun ω => F t ω+
            DampedFixedIntegral.value 𝓕 μ h hh hΛ hκ hκ.le
              (fun _ => constantField κ hκ) stronglyMeasurable_const I₀ t ht ω+
            DampedFixedIntegral.value 𝓕 μ h hh hΛ hell
              (hell.le.trans ((hb 0).1.trans (hb 0).2))
              (coefficientFunction ha hell hb V) hfield I₁ t ht ω) := by
  let G : ℝ≥0 → Ω → StateL2 := fun t ω => F t ω+noiseVersion 𝓕 μ h hh hΛ κ hκ I₀ t ω
  let w' := w+noiseProcess 𝓕 μ h hh hΛ κ hκ I₀
  have hGc : ∀ ω,Continuous (fun t => G t ω) := fun ω =>
    (hFc ω).add (noiseVersion_continuous 𝓕 μ h hh hΛ κ hκ I₀ hpos ω)
  have hGp : StronglyMeasurable[𝓕.predictable] (Function.uncurry G) :=
    hFp.add (noiseVersion_predictable 𝓕 μ h hh hΛ κ hκ I₀ hpos hnull B₀ hBDG₀)
  have hw' : w'=ᵐ[energyMeasure μ h] Function.uncurry G := by
    have hadd := ae_eq_of_ae_eq_trim (Lp.coeFn_add w (noiseProcess 𝓕 μ h hh hΛ κ hκ I₀))
    filter_upwards [hadd,hw,noiseProcess_ae 𝓕 μ h hh hΛ κ hκ I₀ hpos B₀ hBDG₀] with p hp hw hn
    change w' p=G p.1 p.2
    rw [hp]
    change w p+noiseProcess 𝓕 μ h hh hΛ κ hκ I₀ p=G p.1 p.2
    rw [hw,hn]
    rfl
  obtain ⟨v,hv,_⟩ := DampedNonlinearConvolution.exists_unique_forced 𝓕 μ h hh hΛ ha hell hb
    hβ hH hholder hLip hsmall I₁ w'
  obtain ⟨V,hc,hp,he,hf,hmild⟩ := ContinuousDampedForced.continuous_representative
    𝓕 μ h hh hΛ ha hell hb hβ hH hholder I₁ hpos hnull B₁ hBDG₁ G hGc hGp w' hw' v hv
  refine ⟨v,V,hc,hp,he,hf,fun t ht => ?_⟩
  filter_upwards [hmild t ht,noiseVersion_ae 𝓕 μ h hh hΛ κ hκ I₀ hpos B₀ hBDG₀ t ht] with ω hω hN
  change V t ω=G t ω+_ at hω
  dsimp only [G] at hω
  rw [hN] at hω
  exact hω

end SHE.AdditiveHaarForcing
