module

public import SHE.MixedGirsanovWitnessVector
public import SHE.MixedCappedPrefixVolterra
public import SHE.NativeVolterraAlgebra
public import SHE.MixedGirsanovWitnessMild
public import SHE.MixedGirsanovVectorMild
public import SHE.MixedGirsanovDampedMild
public import SHE.HilbertItoNaturality
public import SHE.NativeGirsanovTwoChannelTransport
public import SHE.NativeDampedHaarInput
public import SHE.NativeControlMass
public import SHE.NativeHeatColumnAction
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass
public import SHE.MixedMovingEnergy
public import SHE.MixedAdditiveControl
public import SHE.CappedStochasticExponential

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.MixedGirsanovWitnessBeforeExit
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedMovingEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedMovingEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedMovingEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedMovingEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedMovingEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedMovingEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedMovingEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedMovingEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedMovingEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedMovingEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedMovingEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedMovingEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)


local notation "Raw"=>MixedCappedControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Cap"=>PredictableEnergyCap.capped Raw


local notation "F0"=>fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ
local notation "F1"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "Drift"=>MixedCappedDampedHeatControl.drift
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S


local instance : SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology

open MixedGirsanovVectorMild
local notation "Vec"=>MixedGirsanovVectorMild.vector 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem exists_mild
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hI0:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
    (hI1:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
    (hG:StandardTerminalGirsanov J)(hΛ:0≤Λ)(hH:(H:ℝ)≤1)
    (u:Process (E:=Both RealHaarInput) 𝓕 μ H)
    (hu:u=ᵐ[energyMeasure μ H] Function.uncurry Cap)
    (hcap:∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤1):
    let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
      (StochasticExponential.bracket 𝓕 μ H u)
    ∀[IsProbabilityMeasure Q],μ≪Q→Q≪μ→
    ∃(K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 Q H)
      (T:GirsanovTransportWitness 𝓕 μ Q H J K)
      (A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 Q H),
      T.control=u ∧
      StandardScalarNaturality A0 (leftIntegral 𝓕 Q H K) ∧
      StandardScalarNaturality A1 (rightIntegral 𝓕 Q H K) ∧

      ∀(t:ℝ≥0)(ht:t≤H),∀ᵐω∂Q,PredictableEnergyCap.accumulated Raw t ω<1→
        S.second t ω=Real.exp (-Λ*(t:ℝ)) • NativeHeatObservation.heat (t:ℝ) u₀+
          Λ • NativeClock.volterra Λ (fun s=>S.second s ω) t+
          A0.integral (MixedGirsanovDampedMild.additive 𝓕 H Λ κ hκ Q hΛ hH t ht) ω+
          A1.integral (MixedGirsanovDampedMild.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Q hΛ hH t ht) ω :=by
  dsimp only
  intro hprob hμQ hQμ
  let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u)
  obtain ⟨K,T,A0,A1,hTu,h0,h1,hm⟩:=MixedGirsanovWitnessVector.exists_mild
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hI0 hI1 hG hΛ hH u hu hcap hμQ hQμ
  refine ⟨K,T,A0,A1,hTu,h0,h1,?_⟩
  intro t htH
  filter_upwards [hm t htH] with ω hω hc
  have hv:=MixedCappedPrefixVolterra.no_exit 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S t htH ω hc
  rw [hv,NativeVolterraAlgebra.sub Λ _ _ (S.second_continuous ω) (S.first_continuous ω) t] at hω
  calc
    _=_:=hω
    _=_:=by module
end SHE.MixedGirsanovWitnessBeforeExit
