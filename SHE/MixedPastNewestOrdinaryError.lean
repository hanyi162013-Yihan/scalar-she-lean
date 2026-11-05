module
public import SHE.MixedPastNewestOriginalAverage
public import SHE.MixedPastNewestOrdinaryState
public import SHE.MixedPastNewestFiniteError
public import SHE.MixedPastNewestIntegratedError
public import SHE.ControlledNewestNodeMass
public import SHE.RootSectionAverage
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
namespace SHE.MixedPastNewestOrdinaryError
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestOrdinaryError_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestOrdinaryError_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestOrdinaryError_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestOrdinaryError_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestOrdinaryError_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestOrdinaryError_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestOrdinaryError_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestOrdinaryError_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestOrdinaryError_period : Fact (0<2*π):=⟨by positivity⟩
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

local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "U"=>MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir"=>MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

local notation "Point"=>MixedPastNewestOrdinarySplit.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def errorField (p:(ℝ≥0×Ω)×HeatCircle):ℝ:=
  aU (PredictableScalarField.nativeField (Function.uncurry S.first) p)-
    aV (PredictableScalarField.nativeField (Function.uncurry S.first) p)

/-- The actual ordinary U bracket insertion minus the smooth-companion
insertion, with the original newest time and every old coordinate. -/
def current (k:ℕ)(z:ℝ×(Ω×History HeatCircle k)):ℝ:=
  if (z.1.toNNReal:ℝ)<(carrier Zero k).terminal z.2.2 then
    (∫y,Point aU k z.1.toNNReal z.2.2 z.2.1 y ∂haarAddCircle)-
      (∫y,Point aV k z.1.toNNReal z.2.2 z.2.1 y ∂haarAddCircle)
  else 0

def primitive (k:ℕ)(z:Ω×History HeatCircle k):ℝ:=
  ∫q,current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k (q,z) ∂volume.restrict (Ioc (v:ℝ) (b:ℝ))

theorem current_eq_error
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ)(z:ℝ×(Ω×History HeatCircle k)):
    current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z=
    MixedPastNewestOriginalMass.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k
        (errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) z:=by
  unfold current MixedPastNewestOriginalMass.current MixedPastNewestTimeFields.active
  dsimp only
  by_cases hq:(z.1.toNNReal:ℝ)<(carrier Zero k).terminal z.2.2
  · rw [if_pos hq,if_pos hq]
    have hs:=MixedPastNewestOrdinarySplit.spatial_split 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages k z.1.toNNReal z.2.2 hq z.2.1
    dsimp only [errorField]
    linarith [hs]
  · rw [if_neg hq,if_neg hq]

theorem primitive_eq_error
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ)(z:Ω×History HeatCircle k):
    primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z=
    MixedPastNewestOriginalMass.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k
        (errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) z:=by
  apply integral_congr_ae
  exact ae_of_all _ (fun q=>current_eq_error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages k (q,z))

theorem averaged_eq_drift_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ):
    ∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,
      RootSectionAverage.average R₀ k
        (primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k) z=
      MixedPastNewestIntegratedError.drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 0
          (errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) (z.2,z.1):=by
  let e:=errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hu:Measurable (Function.uncurry S.first):=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hn:=PredictableScalarField.nativeField_measurable hu
  have he:Measurable e:=(haU.comp hn).sub (haV.comp hn)
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hecap(p):|e p|≤2*M:=by
    exact (abs_sub _ _).trans ((add_le_add
      (NonlinearHaarIntegrand.absBound hell hbU _) (NonlinearHaarIntegrand.absBound hell hbV _)).trans_eq (by ring))
  have hs:=MixedPastNewestOriginalAverage.drift_eq_original_average
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages k (2*M) (mul_nonneg (by norm_num) hM) e he hecap
  have hp:(primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k)=
      MixedPastNewestOriginalMass.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k e:=
    funext (primitive_eq_error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages k)
  rw [hp]
  exact hs.mono (fun _ h=>h.symm)

/-- Original finite expansion signs and unit normalizations are retained:
the true ordinary bracket-error primitives are exactly the finite field
whose uniform collision estimate and canonical epsilon limit are proved. -/
theorem canonical_finite_field_eq_ae
    (D:SmoothApproximation.ScalarData)(j:ℕ)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient j)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (depth:ℕ)(w:ℕ→ℝ):
    ∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,
      (∑k∈Finset.range depth,w k*RootSectionAverage.average R₀ k
        (primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k) z)=
      MixedPastNewestFiniteError.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm D j depth w (z.2,z.1):=by
  have he:(errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)=
      MixedPastNewestIntegratedError.coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j:=by
    funext p
    dsimp only [errorField,MixedPastNewestIntegratedError.coefficientError]
    exact congrArg₂ (fun x y:ℝ=>x-y) (congrFun hU _) (congrFun hV _)
  have hall:∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,∀k:ℕ,
      RootSectionAverage.average R₀ k
        (primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k) z=
      MixedPastNewestIntegratedError.drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 0
          (errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) (z.2,z.1):=
    ae_all_iff.mpr (fun k=>averaged_eq_drift_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages k)
  filter_upwards [hall] with z hz
  unfold MixedPastNewestFiniteError.field
  apply Finset.sum_congr rfl
  intro k hk
  rw [hz k,he]

end SHE.MixedPastNewestOrdinaryError
