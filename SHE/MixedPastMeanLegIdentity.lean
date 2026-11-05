module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.ControlledFamilyMeanFirstMoment
public import SHE.PastMeanAbsoluteBudget
public import SHE.MixedPastMeanFirstMoment
public import SHE.MixedPastBaselineFTCIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanLegIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanLegIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanLegIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanLegIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanLegIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanLegIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanLegIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanLegIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanLegIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanLegIdentity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Ref" => (fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2)

/-- The entire native negative-output mean mark, applied to the actual
dependent current difference of the original mixed common-driver pair. -/
def input (k : ℕ) (θ : ℝ) (q : ℝ≥0) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (ω : Ω) : CircleL2 :=
  OneInputOperator.besselHalf mass ρ hmass hρ
    (integralOperator (MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q q t) ω
      (embed (S.second q ω-S.first q ω)))

attribute [local irreducible] cappedAverage MixedPastLiteralPoint.meanField
open GaussianConvolution
local notation "Val"=>MixedPastMeanFirstMoment.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- The EXACT mean leg from the full three-piece actual FTC, with the
reference evaluated at the original random past. -/
def leg (k : ℕ) (θ : ℝ) (q : ℝ≥0) (p : History HeatCircle k) (ω : Ω) : ℝ :=
  ControlledFamilyLegFubini.mean P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    (U ω,Dir ω) k p q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ

/-- Absolute and relative clocks give literally the same mean mark,
including every individual original stopping weight. -/
theorem leg_eq_value
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) (hvq : v≤q) (p : History HeatCircle k)
    (hq : (q:ℝ)<(carrier Zero k).terminal p) (ω : Ω) : leg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q p ω=Val k θ q p ω := by
  have ht:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k p
  have hθt:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (θ,(U ω,Dir ω)) (0,(0,0)) k p
  have hθq : (q:ℝ)≤(carrier (Base (θ,(U ω,Dir ω))) k).terminal p := by rw [hθt];exact hq.le
  have hvq' : (v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq
  unfold leg ControlledFamilyLegFubini.mean
  rw [ht,ite_eq_left (show (v:ℝ)≤(q:ℝ) ∧ (q:ℝ)<(carrier Zero k).terminal p from ⟨hvq',hq⟩),
    MixedPastBaselineFTCIdentity.mean_eq_meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k p θ q hq ω]
  unfold MixedPastMeanFirstMoment.value
  simp only [cappedAverage,min_eq_left hθq]
  congr 1
  unfold ControlledFamilyThreeLeg.sigma ControlledFamilyThreeLeg.target ControlledFamilyThreeLeg.center
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k p]
  apply PiLp.ext
  intro i
  simp only [PhysicalMeanRange.dampedDirection,PiLp.toLp_apply,sub_sub_sub_cancel_right]

theorem leg_zero_of_not_current (k : ℕ) (θ : ℝ) (q : ℝ≥0) (p : History HeatCircle k)
    (hq : ¬(q:ℝ)<(carrier Zero k).terminal p) (ω : Ω) : leg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q p ω=0 := by
  unfold leg ControlledFamilyLegFubini.mean
  rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k p]
  exact ite_eq_right (fun h=>hq h.2)

theorem value_zero_of_not_strict (k : ℕ) (θ : ℝ) (q : ℝ≥0) (p : History HeatCircle k)
    (hp : ¬StrictHistory Zero k p) (ω : Ω) : Val k θ q p ω=0 := by
  have hp' : ¬StrictHistory (Base (θ,(U ω,Dir ω))) k p:=fun hh=>hp
    ((ControlledThetaPhysicalGeometry.strict_iff P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (θ,(U ω,Dir ω)) (0,(0,0)) k p).mp hh)
  have hz : cappedAverage (Base (θ,(U ω,Dir ω))) k q p=fun _ : WordRecursion.State (1+k)=>(0:ℝ) := by
    funext x
    simp only [cappedAverage,test_zero_of_not_strict _ _ _ hp',gaussianAverage,Pi.zero_apply,integral_zero]
  unfold MixedPastMeanFirstMoment.value
  rw [hz]
  have hd : fderiv ℝ (fun _ : WordRecursion.State (1+k)=>(0:ℝ)) (Mean k θ q ω p)=0:=
    (hasFDerivAt_const (0:ℝ) (Mean k θ q ω p)).fderiv
  rw [hd]
  rfl
end SHE.MixedPastMeanLegIdentity
