module

public import SHE.NativeGirsanovWitnessTransport
public import SHE.MixedGirsanovDampedMild
public import SHE.MixedCappedDampedHeatControl
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

namespace SHE.MixedGirsanovWitnessMild
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

open MixedGirsanovDampedMild

/-- The capped actual control gives an exact changed-probability damped
mild equation. The energy-cap indicator remains inside its finite drift. -/
theorem exists_observed_mild
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
      ∀(t:ℝ≥0)(ht:t≤H)(L:RealL2→L[ℝ]ℝ),
      (fun ω=>L (S.second t ω))=ᵐ[Q]
        (fun ω=>Real.exp (-Λ*(t:ℝ))*L (NativeHeatObservation.heat (t:ℝ) u₀)+
          Λ*L (NativeClock.volterra Λ (fun s=>S.first s ω) t)+
          L (A0.integral (additive (𝓕:=𝓕) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) Q hΛ hH t ht) ω)+
          L (A1.integral (residual (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) Q hΛ hH t ht) ω)+
          Λ*∫s,Drift L t s ω ∂timeMeasure H):=by
  dsimp only
  intro hprob hμQ hQμ
  let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u)
  obtain ⟨K,T,A0,A1,hTu,h0,h1,ht⟩:=NativeGirsanovWitnessTransport.exists_transport
    𝓕 μ H J hG u hcap I₀ I₁ hI0 hI1 hμQ hQμ
  refine ⟨K,T,A0,A1,hTu,h0,h1,?_⟩
  intro t htH L
  let v':=additive (𝓕:=𝓕) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) Q hΛ hH t htH
  let w':=residual (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) Q hΛ hH t htH
  have hprod:energyMeasure μ H≪energyMeasure Q H:=
    (Measure.AbsolutelyContinuous.refl (timeMeasure H)).prod hμQ
  have hv:S.controlledAdditiveInput t=ᵐ[energyMeasure μ H] v':=by
    filter_upwards [S.controlled_additive_kernel t htH,
      hprod.ae_le (NativeDampedHaarInput.input_ae 𝓕 Q H hΛ hκ hκ.le F0 stronglyMeasurable_const
        t htH ((show (t:ℝ)≤H by exact_mod_cast htH).trans hH))] with p hp hq
    exact hp.trans hq.symm
  have hw:S.controlledResidualInput t=ᵐ[energyMeasure μ H] w':=by
    filter_upwards [S.controlled_residual_kernel t htH,
      hprod.ae_le (NativeDampedHaarInput.input_ae 𝓕 Q H hΛ hell
        (hell.le.trans ((hbV 0).1.trans (hbV 0).2)) F1 S.second_coefficient t htH
        ((show (t:ℝ)≤H by exact_mod_cast htH).trans hH))] with p hp hq
    exact hp.trans hq.symm
  have hc:∀ᵐp∂energyMeasure μ H,
      inner ℝ (NativeGirsanovTwoChannelTransport.block 𝓕 μ H L
        (S.controlledAdditiveInput t) (S.controlledResidualInput t) p) (u p)=
        -Λ*Drift L t p.1 p.2:=by
    filter_upwards [NativeGirsanovTwoChannelTransport.block_ae 𝓕 μ H L
      (S.controlledAdditiveInput t) (S.controlledResidualInput t),
      S.controlled_additive_kernel t htH,S.controlled_residual_kernel t htH,hu] with p hp hq hr hu
    rw [hp,hq,hr,hu]
    exact MixedCappedDampedHeatControl.channels 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S L t p.1 p.2
  have hs:∀ᵐω∂μ,∀ᵐs∂timeMeasure H,
      inner ℝ (NativeGirsanovTwoChannelTransport.block 𝓕 μ H L
        (S.controlledAdditiveInput t) (S.controlledResidualInput t) (s,ω)) (u (s,ω))=
        -Λ*Drift L t s ω:=by
    have hh:=(Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae hc
    exact Measure.ae_ae_of_ae_prod hh
  filter_upwards [hQμ.ae_le (S.second_mild t htH),hQμ.ae_le hs,
    ht L (S.controlledAdditiveInput t) (S.controlledResidualInput t) v' w' hv hw] with ω hm hs hn
  have hi:(∫s,inner ℝ (NativeGirsanovTwoChannelTransport.block 𝓕 μ H L
      (S.controlledAdditiveInput t) (S.controlledResidualInput t) (s,ω)) (u (s,ω)) ∂timeMeasure H)=
      -Λ*(∫s,Drift L t s ω ∂timeMeasure H):=by
    rw [integral_congr_ae hs,integral_const_mul]
  rw [hi] at hn
  rw [hm]
  simp only [map_add,map_smul,smul_eq_mul]
  change _=Real.exp (-Λ*(t:ℝ))*L (NativeHeatObservation.heat (t:ℝ) u₀)+
    Λ*L (NativeClock.volterra Λ (fun s=>S.first s ω) t)+
    L (A0.integral v' ω)+L (A1.integral w' ω)+Λ*(∫s,Drift L t s ω ∂timeMeasure H)
  linarith only [hn]

end SHE.MixedGirsanovWitnessMild
