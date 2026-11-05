module

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

namespace SHE.MixedGirsanovVectorMild
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

def vector(t s:ℝ≥0)(ω:Ω):RealL2:=
  if s<t ∧ PredictableEnergyCap.accumulated Raw s ω<1 then
    Real.exp (-Λ*((t:ℝ)-(s:ℝ))) •
      NativeHeatObservation.heat ((t:ℝ)-(s:ℝ)) (S.second s ω-S.first s ω) else 0
local notation "Vec"=>vector 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem vector_integrable(t:ℝ≥0)(ω:Ω):Integrable (fun s=>Vec t s ω) (timeMeasure H):=by
  have hD:Continuous (fun s:ℝ≥0=>S.second s ω-S.first s ω):=
    (S.second_continuous ω).sub (S.first_continuous ω)
  have hmap:Continuous (fun s:ℝ≥0=>(((t:ℝ)-(s:ℝ))/NativeHeatObservation.timeScale,
      S.second s ω-S.first s ω)):=
    ((continuous_const.sub continuous_subtype_val).div_const NativeHeatObservation.timeScale).prodMk hD
  have hh:=RealHeat.continuous_realHeat_action.comp hmap
  have hb:Continuous (fun s:ℝ≥0=>Real.exp (-Λ*((t:ℝ)-(s:ℝ))) •
      NativeHeatObservation.heat ((t:ℝ)-(s:ℝ)) (S.second s ω-S.first s ω)):=
    (show Continuous (fun s:ℝ≥0=>Real.exp (-Λ*((t:ℝ)-(s:ℝ)))) by fun_prop).smul hh
  have hm:MeasurableSet {s:ℝ≥0|s<t ∧ PredictableEnergyCap.accumulated Raw s ω<1}:=
    measurableSet_Iio.inter (measurableSet_lt
      (PredictableEnergyCap.accumulated_continuous Raw
        (MixedCappedControl.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) ω).measurable measurable_const)
  apply ((NativeControlMass.continuous_integrable H hb).indicator hm).congr
  exact ae_of_all _ (fun s=>by simp only [Set.indicator_apply,Set.mem_setOf_eq,vector])

theorem map_vector(L:RealL2→L[ℝ]ℝ)(t s:ℝ≥0)(ω:Ω):L (Vec t s ω)=Drift L t s ω:=by
  unfold vector MixedCappedDampedHeatControl.drift
  split_ifs <;> simp only [map_smul,smul_eq_mul,map_zero]

theorem map_integral(L:RealL2→L[ℝ]ℝ)(t:ℝ≥0)(ω:Ω):
    L (∫s,Vec t s ω ∂timeMeasure H)=∫s,Drift L t s ω ∂timeMeasure H:=by
  rw [← L.integral_comp_comm (vector_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S t ω)]
  apply integral_congr_ae
  exact ae_of_all _ (fun s=>map_vector 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S L t s ω)

/-- The literal capped companion satisfies the actual changed-measure
Hilbert mild identity; no new solution law is assumed. -/
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
      (A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 Q H),
      StandardScalarNaturality A0 (leftIntegral 𝓕 Q H K) ∧
      StandardScalarNaturality A1 (rightIntegral 𝓕 Q H K) ∧
      ∀(t:ℝ≥0)(ht:t≤H),S.second t=ᵐ[Q]
        (fun ω=>Real.exp (-Λ*(t:ℝ)) • NativeHeatObservation.heat (t:ℝ) u₀+
          Λ • NativeClock.volterra Λ (fun s=>S.first s ω) t+
          A0.integral (MixedGirsanovDampedMild.additive 𝓕 H Λ κ hκ Q hΛ hH t ht) ω+
          A1.integral (MixedGirsanovDampedMild.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Q hΛ hH t ht) ω+
          Λ • (∫s,Vec t s ω ∂timeMeasure H)):=by
  dsimp only
  intro hprob hμQ hQμ
  let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u)
  obtain ⟨K,A0,A1,h0,h1,ht⟩:=MixedGirsanovDampedMild.exists_observed_mild
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hI0 hI1 hG hΛ hH u hu hcap hμQ hQμ
  refine ⟨K,A0,A1,h0,h1,?_⟩
  intro t htH
  have hz:(fun ω=>S.second t ω-(Real.exp (-Λ*(t:ℝ)) • NativeHeatObservation.heat (t:ℝ) u₀+
      Λ • NativeClock.volterra Λ (fun s=>S.first s ω) t+
      A0.integral (MixedGirsanovDampedMild.additive 𝓕 H Λ κ hκ Q hΛ hH t htH) ω+
      A1.integral (MixedGirsanovDampedMild.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Q hΛ hH t htH) ω+
      Λ • (∫s,Vec t s ω ∂timeMeasure H)))=ᵐ[Q] (0:Ω→RealL2):=by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    filter_upwards [ht t htH L] with ω hω
    change L (_-_)=0
    simp only [map_sub,map_add,map_smul,smul_eq_mul,
      map_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S L t ω]
    exact sub_eq_zero.mpr hω
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

end SHE.MixedGirsanovVectorMild
