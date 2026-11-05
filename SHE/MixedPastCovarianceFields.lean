module

public import SHE.MixedPastLiteralCovariance
public import SHE.MixedPastLiteralFields
public import SHE.MixedPastProfileDerivative
public import SHE.ControlledThetaPhysicalMarkFields
public import SHE.ControlledFamilyProfileMarkFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastLiteralCovariance
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastCovarianceFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastCovarianceFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

/-- Actual signed input in relative reference time. -/
def direction (θ : ℝ) (p : Ω×StoppedGaussianFeatures.Domain) : ℝ :=
  ControlledProfile.derivative P Λ (U p.1) (Dir p.1) (p.2,θ)

/-- Past measurability of the full actual signed profile input. -/
theorem direction_past_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (θ : ℝ) :
    @Measurable (Ω×StoppedGaussianFeatures.Domain) ℝ ((𝓕 v).prod inferInstance) inferInstance
      (direction 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v θ) := by
  have hm := MixedPastProfileDerivative.derivative_past_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hΛ hsmall v
  letI : MeasurableSpace Ω := 𝓕 v
  have hmap : Measurable (fun p : Ω×StoppedGaussianFeatures.Domain=>(p,θ)) :=
    measurable_id.prodMk measurable_const
  convert! hm.comp hmap using 1

/-- Literal covariance point with its actual random past profile
input, rather than an abstract signed field supplied by a caller. -/
def actualPoint (k : ℕ) (θ : ℝ) (q : ℝ≥0) (z : Ω×History X k) : ℝ :=
  point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    k θ q z.2 (direction 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v θ) z.1

theorem actualPoint_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    Measurable (actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hD := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  let a : (Ω×History X k)→Inputs := fun z=>(U z.1,Dir z.1)
  have ha : Measurable a := (hU.comp measurable_fst).prodMk (hD.comp measurable_fst)
  have hc := ControlledFamilyProfileMarkFields.old_profile_variable_measurable P Λ v a ha
  have he := ControlledFamilyProfileMarkFields.profile_direction_variable_measurable P Λ v
    hΛ hsmall a ha (fun _=>θ) measurable_const
  have hm := MixedPastLiteralFields.meanField_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q
  have hh := ControlledThetaPhysicalMarkFields.covariance_point_variable_measurable
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k
    (fun z=>(θ,a z)) (measurable_const.prodMk ha) Prod.snd measurable_snd
    (fun _=>(q:ℝ)) measurable_const
    (fun z=>oldProfile P Λ v (a z.1) z.2)
    (fun z=>ObservationTimeShift.profile (v:ℝ)
      (fun r=>ControlledProfile.derivative P Λ (a z.1).1 (a z.1).2 (r,θ)) z.2) hc he
    (fun z=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q z.1 z.2) hm
  convert! hh using 1

end SHE.MixedPastLiteralCovariance
