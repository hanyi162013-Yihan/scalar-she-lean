module

public import SHE.FixedHorizonCompanion
public import SHE.GivenFirstResidualPair
public import SHE.MixedAdditiveResidualPair
public import SHE.ContinuousControlledCompanion
public import SHE.OrthogonalItoChannels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.GivenFixedHorizonCompanion
open MeasureTheory PredictableL2 LowBands ContinuousHeatMild AdditiveHaarForcing
open AdditiveResidualPair
open scoped NNReal ENNReal
local instance givenFirstResidualPair_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance givenFirstResidualPair_stateSigma : MeasurableSpace StateL2 := borel _
local instance givenFirstResidualPair_stateBorel : BorelSpace StateL2 := ⟨rfl⟩
local instance givenFirstResidualPair_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance givenFirstResidualPair_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
variable (κ : ℝ) (hκ : 0 < κ) {aU aV : ℝ → ℝ}
variable (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0 < ell) (hbU : ∀ z,ell ≤ aU z ∧ aU z ≤ M)
variable (hbV : ∀ z,ell ≤ aV z ∧ aV z ≤ M)

open GivenFirstResidualPair

/-- A given possibly rough first coefficient/solution is preserved
EXACTLY while its smooth controlled companion is constructed on the
same two noise channels. Only the COMPANION coefficient needs a
Lipschitz constant. The prescribed horizon is common to all such coefficients. -/
theorem exists_companion {HV β : ℝ} (hβ : 0<β) (hHV : 0≤HV)
    (hholderV : ∀ z w,|aV z-aV w|≤HV*|z-w|^β) {LV : ℝ≥0}
    (hLipV : LipschitzWith LV (fun z=>(aV z:ℂ)))
    (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ h)
    (hpos : 0<h) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B₀ B₁ : ℝ≥0) (hBDG₀ : StandardTerminalBDG16 I₀ B₀) (hBDG₁ : StandardTerminalBDG16 I₁ B₁)
    (u₀ v₀ : StateL2) (S : FirstSolution 𝓕 μ h hh κ hκ haU hell hbU I₀ I₁ u₀) :
    ∃ T : MixedAdditiveResidualPair.Solution 𝓕 μ h hh hΛ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀,
      T.first=S.value ∧ T.firstProcess=S.process := by
  have hUa : StronglyAdapted 𝓕 S.value :=
    (show IsStronglyPredictable 𝓕 S.value from S.predictable).stronglyAdapted
  let G:=ContinuousControlledCompanion.force (Λ:=Λ) S.value v₀
  have hGc : ∀ ω,Continuous (fun t=>G t ω) :=
    ContinuousControlledCompanion.continuous_force S.value S.continuous v₀
  have hGp : StronglyMeasurable[𝓕.predictable] (Function.uncurry G) :=
    ContinuousControlledCompanion.predictable_force 𝓕 S.value hUa S.continuous v₀
  obtain ⟨v,V,hcV,hpV,heV,hfV,hmildV⟩:=FixedHorizonCompanion.exists_forced
    𝓕 μ h hh hΛ κ hκ I₀ haV hell hbV hβ hHV hholderV hLipV I₁
    hpos hnull B₀ B₁ hBDG₀ hBDG₁ G hGc hGp
    (ControlledForcing.forcing 𝓕 μ h hΛ S.value hUa S.continuous S.process S.ae v₀)
    (ControlledForcing.forcing_ae 𝓕 μ h hΛ S.value hUa S.continuous S.process S.ae v₀)
  exact ⟨⟨S.process,v,S.value,V,S.continuous,hcV,S.predictable,hpV,S.ae,heV,S.coefficient,hfV,S.mild,hmildV⟩,rfl,rfl⟩


end SHE.GivenFixedHorizonCompanion
