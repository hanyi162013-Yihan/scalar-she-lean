module

public import SHE.AdditiveHaarForcing
public import SHE.ContinuousControlledCompanion
public import SHE.OrthogonalItoChannels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.AdditiveResidualPair
open MeasureTheory PredictableL2 LowBands ContinuousHeatMild AdditiveHaarForcing
open scoped NNReal ENNReal
local instance additiveResidualPair_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance additiveResidualPair_stateSigma : MeasurableSpace StateL2 := borel _
local instance additiveResidualPair_stateBorel : BorelSpace StateL2 := ⟨rfl⟩
local instance additiveResidualPair_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance additiveResidualPair_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
variable (κ : ℝ) (hκ : 0 < κ) {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)

def additiveTerminal (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (t : ℝ≥0) (ht : t ≤ h) : Ω → StateL2 :=
  DampedFixedIntegral.value 𝓕 μ h hh hΛ hκ hκ.le
    (fun _ => constantField κ hκ) stronglyMeasurable_const I t ht

/-- The two equations retain the same additive channel and the same
residual Haar channel. In particular this is a different coupling from
using a single Haar factor of the total variance in both equations. -/
structure Solution
    (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (u₀ v₀ : StateL2) where
  firstProcess : Process (E := StateL2) 𝓕 μ h
  secondProcess : Process (E := StateL2) 𝓕 μ h
  first : ℝ≥0 → Ω → StateL2
  second : ℝ≥0 → Ω → StateL2
  first_continuous : ∀ ω,Continuous (fun t => first t ω)
  second_continuous : ∀ ω,Continuous (fun t => second t ω)
  first_predictable : StronglyMeasurable[𝓕.predictable] (Function.uncurry first)
  second_predictable : StronglyMeasurable[𝓕.predictable] (Function.uncurry second)
  first_ae : firstProcess=ᵐ[energyMeasure μ h] Function.uncurry first
  second_ae : secondProcess=ᵐ[energyMeasure μ h] Function.uncurry second
  first_coefficient : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb first)
  second_coefficient : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb second)
  first_mild : ∀ (t : ℝ≥0) (ht : t ≤ h),first t=ᵐ[μ]
    (fun ω => RealHeat.realHeat (t:ℝ) u₀+
      additiveTerminal 𝓕 μ h hh (Λ := 0) (by norm_num) κ hκ I₀ t ht ω+
      DampedFixedIntegral.value 𝓕 μ h hh (Λ := 0) (by norm_num) hell
        (hell.le.trans ((hb 0).1.trans (hb 0).2))
        (coefficientFunction ha hell hb first) first_coefficient I₁ t ht ω)
  second_mild : ∀ (t : ℝ≥0) (ht : t ≤ h),second t=ᵐ[μ]
    (fun ω => Real.exp (-Λ*(t:ℝ)) • RealHeat.realHeat (t:ℝ) v₀+
      Λ • VolterraPath.value Λ (fun s => first s ω) t+
      additiveTerminal 𝓕 μ h hh hΛ κ hκ I₀ t ht ω+
      DampedFixedIntegral.value 𝓕 μ h hh hΛ hell
        (hell.le.trans ((hb 0).1.trans (hb 0).2))
        (coefficientFunction ha hell hb second) second_coefficient I₁ t ht ω)

/-- Construction of the actual continuous additive-plus-residual
controlled pair by two forced Picard fixed points. All convolution maps,
continuous versions and forcing processes are proved constructions. -/
theorem exists_pair {H β : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (hpos : 0 < h) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B₀ B₁ : ℝ≥0) (hBDG₀ : StandardTerminalBDG16 I₀ B₀) (hBDG₁ : StandardTerminalBDG16 I₁ B₁)
    (u₀ v₀ : StateL2) : Nonempty (Solution 𝓕 μ h hh hΛ κ hκ ha hell hb I₀ I₁ u₀ v₀) := by
  let F : ℝ≥0 → Ω → StateL2 := fun t _ => RealHeat.realHeat (t:ℝ) u₀
  have hFc : ∀ ω,Continuous (fun t => F t ω) := by
    intro ω
    have hp : Continuous (fun t : ℝ≥0 => ((t:ℝ),u₀)) := continuous_subtype_val.prodMk continuous_const
    have hc := RealHeat.continuous_realHeat_action.comp hp
    exact hc
  have hFp : StronglyMeasurable[𝓕.predictable] (Function.uncurry F) := HeatInitialProcess.predictable 𝓕 u₀
  obtain ⟨u,U,hcU,hpU,heU,hfU,hmildU⟩ := AdditiveHaarForcing.exists_forced
    𝓕 μ h hh (Λ := 0) (by norm_num) κ hκ I₀ ha hell hb hβ hH hholder hLip hsmall I₁
    hpos hnull B₀ B₁ hBDG₀ hBDG₁ F hFc hFp (HeatInitialProcess.process 𝓕 μ h u₀)
    (HeatInitialProcess.process_ae 𝓕 μ h u₀)
  have haU : StronglyAdapted 𝓕 U := (show IsStronglyPredictable 𝓕 U from hpU).stronglyAdapted
  let G := ContinuousControlledCompanion.force (Λ := Λ) U v₀
  have hGc : ∀ ω,Continuous (fun t => G t ω) := ContinuousControlledCompanion.continuous_force U hcU v₀
  have hGp : StronglyMeasurable[𝓕.predictable] (Function.uncurry G) :=
    ContinuousControlledCompanion.predictable_force 𝓕 U haU hcU v₀
  obtain ⟨v,V,hcV,hpV,heV,hfV,hmildV⟩ := AdditiveHaarForcing.exists_forced
    𝓕 μ h hh hΛ κ hκ I₀ ha hell hb hβ hH hholder hLip hsmall I₁
    hpos hnull B₀ B₁ hBDG₀ hBDG₁ G hGc hGp
    (ControlledForcing.forcing 𝓕 μ h hΛ U haU hcU u heU v₀)
    (ControlledForcing.forcing_ae 𝓕 μ h hΛ U haU hcU u heU v₀)
  exact ⟨⟨u,v,U,V,hcU,hcV,hpU,hpV,heU,heV,hfU,hfV,hmildU,hmildV⟩⟩

/-- Both prescribed channels are obtained by orthogonal restrictions of
one universal terminal Hilbert integral. BDG is inherited, rather than
postulated independently for the two component noises. -/
theorem exists_pair_of_one_integral {H β : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (I : StandardTerminalIto (C := OrthogonalItoChannels.Both RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (hpos : 0 < h) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) (u₀ v₀ : StateL2) :
    Nonempty (Solution 𝓕 μ h hh hΛ κ hκ ha hell hb
      (OrthogonalItoChannels.leftIntegral 𝓕 μ h I) (OrthogonalItoChannels.rightIntegral 𝓕 μ h I) u₀ v₀) :=
  exists_pair 𝓕 μ h hh hΛ κ hκ ha hell hb hβ hH hholder hLip hsmall _ _ hpos hnull B B
    (OrthogonalItoChannels.left_bdg16 𝓕 μ h I B hBDG)
    (OrthogonalItoChannels.right_bdg16 𝓕 μ h I B hBDG) u₀ v₀

end SHE.AdditiveResidualPair
