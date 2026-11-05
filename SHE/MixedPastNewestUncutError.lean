module
public import SHE.OrdinaryInsertionWindow
public import SHE.MixedPastNewestOrdinaryError
public import SHE.MixedPastNewestOrdinarySplit
public import SHE.MixedPastLiteralMean
public import SHE.NewestIntegratedConstants
public import SHE.MixedPastNewestTimeFields
public import SHE.NewestErrorConstants
public import SHE.ScalarApproximationDiscrepancy
public import SHE.PastNewestOldTimeEnergy
public import SHE.MixedPastNewestFields
public import SHE.ParentScoreInput
public import SHE.ParentMeanMass
public import SHE.WeightedSFiniteMoments
public import SHE.PastWordTimeFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestUncutError
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestUncutError_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestUncutError_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestUncutError_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestUncutError_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestUncutError_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestUncutError_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestUncutError_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestUncutError_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestUncutError_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
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
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

open HistoryProductMeasure OrderedHeatForests
open ActualMeanKernel
local notation "Active"=>MixedPastNewestFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

local notation "InputsAt"=>fun ω:Ω=>(MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v ω,
  MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v ω)
local notation "Point"=>MixedPastNewestOrdinarySplit.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def difference (k:ℕ)(z:Ω×History HeatCircle k):ℝ:=
  ActualUncutRemainder.value (Base (0,InputsAt z.1)) (fun r=>κ+aU r)
    (dU).physicalState (dU).physicalField k z.2 z.1-
  ActualUncutRemainder.value (Base (0,InputsAt z.1)) (fun r=>κ+aV r)
    (dU).physicalState (dU).physicalField k z.2 z.1

theorem point_eq_full_inserted
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (a:ℝ→ℝ)(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(hvq:v≤q)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω)(y:HeatCircle):
    Point a k q h ω y=
      PhysicalIto.insertedWord ((carrier (Base (0,InputsAt ω)) k).window h) (fun r=>κ+a r)
        (fun t=>(dU).physicalState (ω,t)) (fun p=>(dU).physicalField (ω,p))
        (UncutSmoothWords.test (Base (0,InputsAt ω)) k h) q y:=by
  have hterm:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,InputsAt ω) (0,(0,0)) k h
  have hmem:(q:ℝ)∈Icc ((carrier (Base (0,InputsAt ω)) k).window h).left
      ((carrier (Base (0,InputsAt ω)) k).window h).right:=by
    constructor
    · exact_mod_cast hvq
    · change (q:ℝ)≤(carrier (Base (0,InputsAt ω)) k).terminal h
      rw [hterm]
      exact hq.le
  unfold PhysicalIto.insertedWord
  rw [PhysicalIto.backward_eq_semigroup _ _ hmem]
  have he:=MixedPastNewestOrdinaryState.point_eq_observed_insertion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop a k h q hq ω y
  dsimp only at he
  unfold WordRecursion.gaussianSemigroup
  unfold GaussianConvolution.gaussianAverage at he
  exact he

/-- The bounded positive first-hit field is exactly the ordinary
actual-minus-companion remainder of the original full uncut word,
with its random past reference inputs retained pointwise. -/
theorem primitive_eq_difference
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(z:Ω×History HeatCircle k):
    MixedPastNewestOrdinaryError.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z=
        difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k z:=by
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hcapU(r):|κ+aU r|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbU r).1))]
    exact add_le_add le_rfl (hbU r).2
  have hcapV(r):|κ+aV r|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbV r).1))]
    exact add_le_add le_rfl (hbV r).2
  unfold difference
  rw [OrdinaryInsertionWindow.value_sub_eq_mask (Base (0,InputsAt z.1)) (dU).physicalState (dU).physicalField
    (fun r=>κ+aU r) (fun r=>κ+aV r) (measurable_const.add haU)
    (measurable_const.add haV) (add_nonneg hκ.le hM) hcapU (add_nonneg hκ.le hM) hcapV
    (dU).physicalState_measurable (dU).physicalField_measurable]
  unfold MixedPastNewestOrdinaryError.primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hqin
  have hqq:(q.toNNReal:ℝ)=q:=Real.coe_toNNReal q (v.2.trans hqin.1.le)
  have hvq:v≤q.toNNReal:=by
    apply NNReal.coe_le_coe.mp
    simpa only [hqq] using hqin.1.le
  have hterm:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,InputsAt z.1) (0,(0,0)) k z.2
  unfold MixedPastNewestOrdinaryError.current
  dsimp only
  rw [hterm]
  simp only [hqq]
  split_ifs with hq
  · congr 1
    · apply integral_congr_ae
      filter_upwards with y
      simpa only [hqq] using point_eq_full_inserted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm hages hrootStop aU k z.2 q.toNNReal hvq
          (by simpa only [hqq] using hq) z.1 y
    · apply integral_congr_ae
      filter_upwards with y
      simpa only [hqq] using point_eq_full_inserted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm hages hrootStop aV k z.2 q.toNNReal hvq
          (by simpa only [hqq] using hq) z.1 y
  · rfl

/-- Exact root-retained finite error in the ordinary uncut expansion.
It is the same field for which the common, derivative-independent
canonical approximation estimate has already been proved. -/
theorem canonical_finite_error_eq_ae
    (D:SmoothApproximation.ScalarData)(j:ℕ)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient j)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (depth:ℕ)(w:ℕ→ℝ):
    ∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,
      (∑k∈Finset.range depth,w k*RootSectionAverage.average
        (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) k
        (difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k) z)=
      MixedPastNewestFiniteError.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm D j depth w (z.2,z.1):=by
  have hs:=MixedPastNewestOrdinaryError.canonical_finite_field_eq_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    D j hU hV hages depth w
  have he(k:ℕ):
      difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k=
      MixedPastNewestOrdinaryError.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k:=
    funext (fun z=>(primitive_eq_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k z).symm)
  filter_upwards [hs] with z hz
  simp only [he]
  exact hz

end SHE.MixedPastNewestUncutError
