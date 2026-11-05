module

public import SHE.MixedGlobalCurrent
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
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedCappedControl
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


/-- The sign dictated by exp(-J(u)-bracket/2): the changed Brownian
additive channel is W minus the damping control. -/
def raw(t:ℝ≥0)(ω:Ω):Both RealHaarInput:=
  left (-MixedAdditiveControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (t,ω))
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

/-- The actual additive physical drift has the negative sign needed
to remove the companion's minus-Lambda damping under Girsanov. -/
theorem reconstruct(t:ℝ≥0)(ω:Ω):
    realPart (fieldFactor κ κ hκ (AdditiveHaarForcing.constantField κ hκ)
      (realInputEmbed ((Raw t ω).ofLp.1)))= -(Λ • (S.second t ω-S.first t ω)):=by
  change realPart (fieldFactor κ κ hκ (AdditiveHaarForcing.constantField κ hκ)
    (realInputEmbed (-MixedAdditiveControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (t,ω))))=_
  rw [AdditivePhysicalFactor.factor_constant,map_neg,smul_neg,
    ←AdditivePhysicalFactor.factor_constant]
  exact congrArg Neg.neg (MixedAdditiveControl.reconstruct
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (t,ω))

theorem norm_sq(p:ℝ≥0×Ω):‖Raw p.1 p.2‖^2=(Λ^2/κ)*‖S.second p.1 p.2-S.first p.1 p.2‖^2:=by
  rw [raw,LinearIsometry.norm_map,norm_neg]
  exact AdditiveHaarControl.norm_sq κ hκ Λ _

theorem continuous(ω:Ω):Continuous (fun t=>Raw t ω):=
  left.continuous.comp ((AdditiveHaarControl.continuous κ hκ Λ).comp
    ((S.second_continuous ω).sub (S.first_continuous ω))).neg

theorem predictable:StronglyMeasurable[𝓕.predictable] (Function.uncurry Raw):=
  left.continuous.comp_stronglyMeasurable
    (MixedAdditiveControl.predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).neg

theorem adapted:StronglyAdapted 𝓕 Raw:=
  (show IsStronglyPredictable 𝓕 Raw from
    predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).stronglyAdapted

theorem energy:(∫p,‖Raw p.1 p.2‖^2 ∂energyMeasure μ H)=(Λ^2/κ)*Global:=by
  simp_rw [norm_sq]
  exact integral_const_mul _ _

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ in
/-- Actual same-original-noise capped-control exponential witnesses;
the expected cost is bounded by the coupled solution's true global
energy. No canonical SPDE law is supplied as an input. -/
theorem exists_witness (hΛ:0≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)
    (hBDG:StandardTerminalBDGPower 1 J B)(hNovikov:StandardTerminalNovikov J):
    ∃(u:Process (E:=Both RealHaarInput) 𝓕 μ H)(V:Ω→ℝ),
      u=ᵐ[energyMeasure μ H] Function.uncurry (PredictableEnergyCap.capped Raw) ∧
      Measurable V ∧ V=ᵐ[μ] StochasticExponential.bracket 𝓕 μ H u ∧
      (∀ω,0≤V ω ∧ V ω≤1 ∧ V ω≤PredictableEnergyCap.accumulated Raw H ω) ∧
      Integrable V μ ∧
      Integrable (fun ω=>Real.exp (-J.integral u ω-V ω/2)) μ ∧
      (∫ω,Real.exp (-J.integral u ω-V ω/2) ∂μ)=1 ∧
      ‖u‖^2≤(Λ^2/κ)*Global:=by
  have hd:=MixedMovingEnergy.global_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG
  have hi:Integrable (fun p:ℝ≥0×Ω=>‖Raw p.1 p.2‖^2) (energyMeasure μ H):=by
    convert! hd.const_mul (Λ^2/κ) using 1
    funext p
    exact norm_sq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S p
  obtain ⟨u,V,hu,hm,hv,hb,hvi,hzi,hz,hcost⟩:=CappedStochasticExponential.exists_witness
    𝓕 μ H Raw (adapted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)
    (continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) J hNovikov hi
  refine ⟨u,V,hu,hm,hv,hb,hvi,hzi,hz,?_⟩
  exact hcost.trans_eq (energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)
end SHE.MixedCappedControl
