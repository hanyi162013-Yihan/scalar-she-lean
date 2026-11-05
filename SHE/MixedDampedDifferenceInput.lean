module

public import SHE.HeatObservationUniqueness
public import SHE.NativeFixedHaarInput
public import SHE.NativeDampedObservation
public import SHE.MixedNativePairObservation
public import SHE.HeatedDifferenceMoments
public import SHE.MixedCurrentInputMoments

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedDampedDifferenceInput
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (hΛ:0≤Λ) (hH:(H:ℝ)≤1)
local notation "hM"=>(hell.le.trans ((hbU 0).1.trans (hbU 0).2))
local notation "fU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "fV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

def first_input (q:ℝ≥0) (hq:q≤H):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ q)
    (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q)
    (NativeFixedHaarInput.input 𝓕 μ H hell hM fU S.first_coefficient q hq
      ((by exact_mod_cast hq : (q:ℝ)≤(H:ℝ)).trans hH))

theorem first_input_ae (q:ℝ≥0) (hq:q≤H):
    first_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq=ᵐ[energyMeasure μ H]
      fun p=>Real.exp (-Λ*((q:ℝ)-(p.1:ℝ))) •
        kernel ell M hell ((q:ℝ)-(p.1:ℝ),fU p):=by
  filter_upwards [PredictableContraction.weighted_ae 𝓕 μ H (PredictableDamping.weight Λ q)
    (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q)
    (NativeFixedHaarInput.input 𝓕 μ H hell hM fU S.first_coefficient q hq
      ((by exact_mod_cast hq : (q:ℝ)≤(H:ℝ)).trans hH)),
    NativeFixedHaarInput.input_ae 𝓕 μ H hell hM fU S.first_coefficient q hq
      ((by exact_mod_cast hq : (q:ℝ)≤(H:ℝ)).trans hH)] with p hp hr
  change first_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq p=_ at hp ⊢
  rw [hp,hr]
  dsimp only [NativeFixedHaarInput.raw]
  by_cases hs:(p.1:ℝ)≤(q:ℝ)
  · rw [PredictableDamping.weight_eq hs]
  · rw [kernel_zero hell (sub_nonpos.mpr (le_of_not_ge hs)) (fU p),smul_zero,smul_zero]

def input (q:ℝ≥0) (hq:q≤H):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  S.controlledResidualInput q-first_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ in
/-- The actual controlled difference equals the integral of the literal
signed damped original-Haar input. Shared additive noise and the drift
resolvent have been cancelled, rather than supplied as an isometry model. -/
theorem representation (q:ℝ≥0) (hq:q≤H):
    (fun ω=>S.second q ω-S.first q ω)=ᵐ[μ]
      I₁.integral (input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq):=by
  let R:=input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq
  apply HeatObservationUniqueness.ae_eq μ _ _
    (MixedHeatedDifferenceMoments.difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q)
    (Lp.stronglyMeasurable _).measurable
  intro ε hε x
  let T:ℝ:=(q:ℝ)+ε
  have hT:(q:ℝ)<T:=by dsimp only [T];linarith
  have hτ:T-(q:ℝ)=ε:=by dsimp only [T];ring
  have hobs:=MixedNativePairResolvent.difference_observation
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hΛ q hq hT x
  have hr:((columnFunctional (T-(q:ℝ)) x).compLpL 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕))) R=
      NativeHybridInput.dampedDifference 𝓕 μ H hell hM fU fV
        S.first_coefficient S.second_coefficient q hT x hΛ:=by
    dsimp only [R,input]
    rw [map_sub,
      NativeDampedObservation.observed_input_eq 𝓕 μ H hΛ hell hM fV S.second_coefficient hT x
        (S.controlledResidualInput q) (S.controlled_residual_kernel q hq),
      NativeDampedObservation.observed_input_eq 𝓕 μ H hΛ hell hM fU S.first_coefficient hT x
        _ (first_input_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq)]
    exact (PredictableWeightedAlgebra.weighted_sub 𝓕 μ H (PredictableDamping.weight Λ q)
      (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q) _ _).symm
  have he:=hIJ₁.commutes (functional (T-(q:ℝ)) x) R
  change ((functional (T-(q:ℝ)) x).compLpL 2 μ) (I₁.integral R)=
    (rightIntegral 𝓕 μ H J).integral
      (((columnFunctional (T-(q:ℝ)) x).compLpL 2
        ((energyMeasure μ H).trim (predictable_le_product 𝓕))) R) at he
  rw [hr] at he
  have hc:=(functional (T-(q:ℝ)) x).coeFn_compLpL (I₁.integral R)
  rw [he] at hc
  filter_upwards [hobs,hc] with ω ho hi
  simp only [hτ,sub_self,map_zero,mul_zero,zero_add] at ho hi
  exact ho.trans hi

end SHE.MixedDampedDifferenceInput
