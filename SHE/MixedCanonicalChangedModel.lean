module
public import SHE.MixedCappedControl
public import SHE.MixedCappedGirsanovDriver
public import SHE.CappedGirsanovDriver
public import SHE.MixedGirsanovWitnessBeforeExit
public import SHE.SelectedGirsanovSmoothModel
public import SHE.StandardChangedHilbertBDG
public import SHE.NativeStoppedPathComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
namespace SHE.MixedCanonicalChangedModel
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance :Fact (0<2*Real.pi):=⟨by positivity⟩
local instance :Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance :MeasurableSpace RealL2:=borel _
local instance :BorelSpace RealL2:=⟨rfl⟩
local instance :MeasurableSpace CircleL2:=borel _
local instance :BorelSpace CircleL2:=⟨rfl⟩
local instance :MeasurableSpace RealHaarInput:=borel _
local instance :BorelSpace RealHaarInput:=⟨rfl⟩
local instance :MeasurableSpace (Both RealHaarInput):=borel _
local instance :BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance :MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance :BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Raw"=>MixedCappedControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Rows"=>CappedGirsanovDriver.originalRow 𝓕 μ H
local notation "Coordinates"=>CappedGirsanovDriver.originalCoordinate 𝓕 μ H J


variable (hΛ:0≤Λ)(hH:(H:ℝ)≤1) {β L:ℝ} (hβ:0<β)(hL:0≤L)
  (hholder:∀z w,|aV z-aV w|≤L*|z-w|^β)

/-- One actual companion, one capped measure, one changed driver, and
one smooth model constructed on its SAME natural Hilbert channels. -/
structure Data where
  control:Process (E:=Both RealHaarInput) 𝓕 μ H
  capped:control=ᵐ[energyMeasure μ H] Function.uncurry (PredictableEnergyCap.capped Raw)
  cap:∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H control ω≤1
  Q:Measure Ω
  probability:IsProbabilityMeasure Q
  measure_eq:Q=ExponentialChangeMeasure.measure μ (fun ω=>J.integral control ω)
    (StochasticExponential.bracket 𝓕 μ H control)
  original_ac:μ≪Q
  changed_ac:Q≪μ
  K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 Q H
  transport:GirsanovTransportWitness 𝓕 μ Q H J K
  transport_control:transport.control=control
  A0:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 Q H
  A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 Q H
  smooth:letI:=probability
    SelectedGirsanovSmoothModel.Data 𝓕 Q H hH κ hκ haV hell hbV hβ hL hholder K A0 A1 u₀
  mild:∀(t:ℝ≥0)(ht:t≤H),∀ᵐω∂Q,PredictableEnergyCap.accumulated Raw t ω<1→
    S.second t ω=Real.exp (-Λ*(t:ℝ)) • NativeHeatObservation.heat (t:ℝ) u₀+
      Λ • NativeClock.volterra Λ (fun s=>S.second s ω) t+
      A0.integral (MixedGirsanovDampedMild.additive 𝓕 H Λ κ hκ Q hΛ hH t ht) ω+
      A1.integral (MixedGirsanovDampedMild.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Q hΛ hH t ht) ω
  compare:∀(f g:Ω→ℝ)(B:ℝ),AEStronglyMeasurable f μ→AEStronglyMeasurable g μ→
    0≤B→(∀ω,|f ω|≤B)→(∀ω,|g ω|≤B)→
    (∀ω,ω∉{ω|1≤PredictableEnergyCap.accumulated Raw H ω}→f ω=g ω)→
    |(∫ω,f ω ∂μ)-(∫ω,g ω ∂Q)|≤2*B*(Real.sqrt ((Λ^2/κ)*Global)+(Λ^2/κ)*Global)



/-- The actual smooth solution on the selected changed measure. -/
def Data.solution
    (D:Data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hΛ hH hβ hL hholder):
    letI:=D.probability
    NativeMildFirst.Data 𝓕 D.Q H κ hκ haV hell hbV D.A0 D.A1 u₀:=by
  letI:=D.probability
  exact SelectedGirsanovSmoothModel.Data.solution
    𝓕 D.Q H hH κ hκ haV hell hbV hβ hL hholder D.K D.A0 D.A1 u₀ D.smooth

include hIJ₀ hIJ₁ in
/-- Construct all selected changed-law data from the actual coupling.
The smooth model and before-exit equation retain the same K,T,A0,A1. -/
theorem exists_data {Lip:ℝ≥0}(hLip:LipschitzWith Lip (fun z=>(aV z:ℂ)))
    (hNovikov:StandardTerminalNovikov J)(hG:StandardTerminalGirsanov J)
    (hpos:0<H)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hlocal:StandardTerminalPastLocality J)
    (B1 B16:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)(hBDG16:StandardTerminalBDG16 J B16)
    (hOrdinaryBDG:StandardChangedHilbertBDG 𝓕 μ H J):
    Nonempty (Data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hΛ hH hβ hL hholder):=by
  obtain ⟨u,hu,hcap,hprob,hμQ,hQμ,hr,hrm,hK,hexit,hTV,hcompare⟩:=
    MixedCappedGirsanovDriver.exists_changed_driver
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
      NativeTwoChannelNoiseBasis.both NativeTwoChannelNoiseBasis.both_orthonormal
      hNovikov hG hΛ hH hpos hnull B1 B16 hBDG1 hBDG16
  let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u)
  letI:IsProbabilityMeasure Q:=hprob
  obtain ⟨K,T,A0,A1,hTu,h0,h1,hm⟩:=MixedGirsanovWitnessBeforeExit.exists_mild
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hG hΛ hH u hu hcap hμQ hQμ
  have hcT:∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H T.control ω≤1:=by
    rw [hTu]
    exact hcap
  have heT:Q=ExponentialChangeMeasure.measure μ (fun ω=>J.integral T.control ω)
      (StochasticExponential.bracket 𝓕 μ H T.control):=by
    rw [hTu]
  obtain ⟨W⟩:=SelectedGirsanovSmoothModel.exists_data
    𝓕 Q H hH κ hκ haV hell hbV hβ hL hholder K A0 A1 u₀ hLip μ J T
    hμQ hQμ hlocal B16 hBDG16 hpos hnull hG hcT heT h0 h1 (hOrdinaryBDG Q K T hμQ hQμ hnull hlocal hpos hH hcT heT)
  exact ⟨⟨u,hu,hcap,Q,hprob,rfl,hμQ,hQμ,K,T,hTu,A0,A1,W,hm,hcompare⟩⟩

end SHE.MixedCanonicalChangedModel
