module
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestOrdinaryState
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestOrdinaryState_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestOrdinaryState_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestOrdinaryState_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestOrdinaryState_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestOrdinaryState_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestOrdinaryState_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestOrdinaryState_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestOrdinaryState_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestOrdinaryState_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
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

/-- Before the next old insertion, theta zero is exactly the ordinary
U observation, with every original target and stop unchanged. This is
an equality for every current sample, not an AE field substitution. -/
theorem mean_zero_eq_observe
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    Mean k 0 q ω h=WordRecursion.observe
      (fun t=>(dU).physicalState (ω,t)) (fun p=>(dU).physicalField (ω,p))
      ((carrier Zero k).observations.observations h) q:=by
  rw [MixedPastLiteralMean.meanField_eq_jointMeanVector
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      hages hrootStop k h 0 q hq ω,
    ControlledJointWeightedWord.jointMeanVector_zero]
  apply PiLp.ext
  intro i
  have ht:=carrier_targets_after Zero h hages hq i
  simp only [PhysicalMeanRange.currentDirection,WithLp.ofLp_toLp,WordRecursion.observe,
    ite_eq_left ht,MixedNativeJointHistory.firstData,PredictableWordState.Data.physicalState,
    Real.toNNReal_coe,Function.uncurry]
  dsimp only [StoppedGaussianScore.nativeCenter]
  rw [NativeHeatSpan.scale_inverse]
  rfl

/-- The old Gaussian state used by the repaired error is the literal
ordinary U-side state in the finite physical Ito insertion. -/
theorem point_eq_observed_insertion
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (a:ℝ→ℝ)(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω)(y:HeatCircle):
    let inputs:Inputs:=(MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v ω,
      MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v ω)
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb inputs
    let L:=Base (0,inputs)
    let ZZ:=((carrier L k).observations.observations h)
    let G:=gaussianAverage (WordRecursion.covariance R.reference ZZ q ((carrier L k).terminal h))
      (UncutSmoothWords.test L k h)
    MixedPastNewestOrdinarySplit.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm a k q h ω y=
    WordRecursion.insertion (fun z=>κ+a z) R.reference ZZ q y G
      (WordRecursion.observe (fun t=>(dU).physicalState (ω,t)) (fun p=>(dU).physicalField (ω,p))
        (appendObservation ZZ q y) q):=by
  dsimp only
  rw [WordRecursion.insertion_observe]
  simp only [MixedPastNewestOrdinarySplit.point,JointPhysicalInsertion.insertion_appendState]
  rw [mean_zero_eq_observe 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω]
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    (0,(0,0)) (0,(MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v ω,
      MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v ω)) k h]
  simp only [WordRecursion.directionalSecond,WordRecursion.hessian,GaussianTaylor.hessian,
    MixedNativeJointHistory.firstData,PredictableWordState.Data.physicalField,
    PredictableScalarField.wordField,Real.toNNReal_coe]

/-- Exact physical ordinary-U bracket split after its native spatial
integral. It keeps the original U observation in every old coordinate;
the displayed newest error is the already bounded literal insertion. -/
theorem observed_spatial_split
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    let inputs:Inputs:=(MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v ω,
      MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v ω)
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb inputs
    let L:=Base (0,inputs)
    let ZZ:=((carrier L k).observations.observations h)
    let G:=gaussianAverage (WordRecursion.covariance R.reference ZZ q ((carrier L k).terminal h))
      (UncutSmoothWords.test L k h)
    (∫y,WordRecursion.insertion (fun z=>κ+aU z) R.reference ZZ q y G
      (WordRecursion.observe (fun t=>(dU).physicalState (ω,t)) (fun p=>(dU).physicalField (ω,p))
        (appendObservation ZZ q y) q) ∂haarAddCircle)=
    (∫y,WordRecursion.insertion (fun z=>κ+aV z) R.reference ZZ q y G
      (WordRecursion.observe (fun t=>(dU).physicalState (ω,t)) (fun p=>(dU).physicalField (ω,p))
        (appendObservation ZZ q y) q) ∂haarAddCircle)+
    Value k 0 q h (fun z=>aU (PredictableScalarField.nativeField (Function.uncurry S.first) ((q,z.1),z.2))-
      aV (PredictableScalarField.nativeField (Function.uncurry S.first) ((q,z.1),z.2))) ω:=by
  dsimp only
  have hs:=MixedPastNewestOrdinarySplit.spatial_split
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages k q h hq ω
  have hU:=integral_congr_ae (μ:=haarAddCircle) (ae_of_all _ (fun y=>point_eq_observed_insertion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages hrootStop aU k h q hq ω y))
  have hV:=integral_congr_ae (μ:=haarAddCircle) (ae_of_all _ (fun y=>point_eq_observed_insertion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages hrootStop aV k h q hq ω y))
  rw [hU,hV] at hs
  exact hs

end SHE.MixedPastNewestOrdinaryState
