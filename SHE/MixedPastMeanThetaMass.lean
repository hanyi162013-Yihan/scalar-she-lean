module

public import SHE.MixedNativeRootLegMass

public import SHE.FamilyMeanCoordinates
public import SHE.MixedPastMeanLegIdentity
public import SHE.NativeFourierAverage
public import SHE.MixedPastMeanSupport
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

namespace SHE.MixedPastMeanThetaMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanThetaMass_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanThetaMass_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanThetaMass_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanThetaMass_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanThetaMass_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanThetaMass_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastMeanThetaMass_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanThetaMass_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanThetaMass_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

local notation "Input"=>MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Leg"=>MixedPastMeanLegIdentity.leg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

local notation "RawMean"=>MixedNativeRootLegMass.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

theorem meanField_measurable (k : ℕ) (q : ℝ≥0) : Measurable (RawMean k q) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hD := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hUq := embed.continuous.measurable.comp
    (((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted q).measurable.mono (𝓕.le q) le_rfl)
  have hDq := embed.continuous.measurable.comp
    ((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted q).sub
      ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted q)).measurable.mono (𝓕.le q) le_rfl)
  exact ControlledFamilyMeanFieldsBorel.mean_variable_measurable P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k
    (fun z : ℝ×(Ω×History HeatCircle k)=>(U z.2.1,Dir z.2.1))
    ((hU.comp measurable_snd.fst).prodMk (hD.comp measurable_snd.fst))
    (fun z=>z.2.2) measurable_snd.snd (fun _=>(q:ℝ)) measurable_const
    (fun z=>embed (S.first q z.2.1)) (fun z=>embed (S.second q z.2.1-S.first q z.2.1))
    (hUq.comp measurable_snd.fst) (hDq.comp measurable_snd.fst) Prod.fst measurable_fst

include hIJ₀ hIJ₁ in
/-- Honest absolute interpolation/sample/history mass of the actual mean
leg alone; no covariance/profile-derivative smallness premise is needed. -/
theorem actual_theta_integrable (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Babs : ℝ≥0) (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    Integrable (RawMean k q) ((volume.restrict (Ioc (0:ℝ) 1)).prod
      (μ.prod (historyMeasure (Ref (0,(0,0))) haarAddCircle k))) := by
  let C:=MixedPastWordMoments.momentConstant P k k 1
    ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)
  let K:=sqrt (∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ)*
    (sqrt C*((1+k:ℕ):ℝ)*sqrt (2*UniformFutureProfileScores.constant (1+k)/P.lower))
  let Em:=K*((haarAddCircle : Measure HeatCircle).real univ*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*
    QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
      ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (1/2:ℝ) A0 ν)
  have hs : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z=>RawMean k q (θ,z)) (μ.prod (historyMeasure (Ref (0,(0,0))) haarAddCircle k)) ∧
        (∫ z,|RawMean k q (θ,z)| ∂μ.prod (historyMeasure (Ref (0,(0,0))) haarAddCircle k))≤Em := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hh:=MixedPastMeanAbsolute.actual_absolute_history 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hrootTarget
      hspan haarAddCircle k hfresh hold θ htθ A0 ν hA0 hν hjet Babs hBDGabs q hvq hqb hqH hq1
    simpa only [MixedNativeRootLegMass.meanField,MixedPastMeanLegIdentity.leg,C,K,Em] using hh
  exact (SectionFirstMoment.joint_integrable (μ.prod (historyMeasure (Ref (0,(0,0))) haarAddCircle k))
    (volume.restrict (Ioc (0:ℝ) 1)) _ ((meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q).comp measurable_swap)
    (fun _=>Em) (integrable_const Em) hs).1.swap

end SHE.MixedPastMeanThetaMass

