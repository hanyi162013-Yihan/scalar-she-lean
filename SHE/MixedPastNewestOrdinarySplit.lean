module
public import SHE.MixedPastNewestApproximation
public import SHE.JointPhysicalInsertion
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
namespace SHE.MixedPastNewestOrdinarySplit
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestOrdinarySplit_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestOrdinarySplit_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestOrdinarySplit_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestOrdinarySplit_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestOrdinarySplit_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestOrdinarySplit_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestOrdinarySplit_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestOrdinarySplit_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestOrdinarySplit_period : Fact (0<2*π):=⟨by positivity⟩
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

local notation "U"=>MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir"=>MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "nativeU"=>PredictableScalarField.nativeField (Function.uncurry S.first)
local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- Ordinary U-side insertion at the actual newest U field. Both old
coordinates and the full original q covariance are retained. -/
def point (a:ℝ→ℝ)(k:ℕ)(q:ℝ≥0)(h:History HeatCircle k)(ω:Ω)(y:HeatCircle):ℝ:=
  let p:ℝ×Inputs:=(0,(U ω,Dir ω))
  WordRecursion.insertion (fun z=>κ+a z)
    (referenceData P P.coefficient haP Λ p.1 v b hvb p.2).reference
    ((carrier (Base p) k).observations.observations h) q y
    (gaussianAverage (WordRecursion.covariance
      (referenceData P P.coefficient haP Λ p.1 v b hvb p.2).reference
      ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h))
    (JointPhysicalInsertion.appendState (nativeU ((q,ω),y)) (Mean k 0 q ω h))

theorem point_split (k:ℕ)(q:ℝ≥0)(h:History HeatCircle k)(ω:Ω)(y:HeatCircle):
    point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm aU k q h ω y=
    point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm aV k q h ω y+
      (1/2:ℝ)*(aU (nativeU ((q,ω),y))-aV (nativeU ((q,ω),y)))*
        WordRecursion.directionalSecond
          (gaussianAverage (WordRecursion.covariance
            (referenceData P P.coefficient haP Λ 0 v b hvb (U ω,Dir ω)).reference
            ((carrier (Base (0,(U ω,Dir ω))) k).observations.observations h) q
            ((carrier (Base (0,(U ω,Dir ω))) k).terminal h))
              (UncutSmoothWords.test (Base (0,(U ω,Dir ω))) k h)) (Mean k 0 q ω h)
          (heatRow ((carrier (Base (0,(U ω,Dir ω))) k).observations.observations h) q y):=by
  simp only [point,JointPhysicalInsertion.insertion_appendState,WordRecursion.directionalSecond,
    WordRecursion.hessian,GaussianTaylor.hessian]
  ring

theorem point_integrable (a:ℝ→ℝ)(ha:Measurable a)(hab:∀z,ell≤a z∧a z≤M)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ)(q:ℝ≥0)(h:History HeatCircle k)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    Integrable (point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm a k q h ω) haarAddCircle:=by
  let p:ℝ×Inputs:=(0,(U ω,Dir ω))
  let R:=referenceData P P.coefficient haP Λ 0 v b hvb p.2
  let ZZ:=((carrier (Base p) k).observations.observations h)
  let G:=gaussianAverage (WordRecursion.covariance R.reference ZZ q ((carrier (Base p) k).terminal h))
    (UncutSmoothWords.test (Base p) k h)
  let c:ℝ×HeatCircle→ℝ:=fun z=>κ+a (nativeU ((q,ω),z.2))-R.reference (q,z.2)
  have hu:Measurable (Function.uncurry S.first):=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hm:=PredictableScalarField.nativeField_measurable hu
  have hc:Measurable c:=(measurable_const.add
    (ha.comp (hm.comp (measurable_const.prodMk measurable_snd)))).sub
      (R.reference_measurable.comp (measurable_const.prodMk measurable_snd))
  have hM:0≤M:=hell.le.trans ((hab 0).1.trans (hab 0).2)
  have hqp:(q:ℝ)<(carrier (Base p) k).terminal h:=by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0))]
    exact hq
  have hgap:∀i,(carrier (Base p) k).terminal h≤(ZZ i).target:=by
    intro i
    exact ((carrier (Base p) k).stops_after h i).trans
      (RecursiveScoreSupport.carrier_ages (Base p) hages k h i)
  have hbnd(y:HeatCircle):|c (q,y)|≤κ+M+P.upper:=by
    have hb:|κ+a (nativeU ((q,ω),y))|≤κ+M:=by
      rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hab _).1))]
      linarith [(hab (nativeU ((q,ω),y))).2]
    have hr:|R.reference (q,y)|≤P.upper:=by
      have hb:=coefficient_bounds P Λ 0 v p.2 (q,y)
      change |coefficient P Λ 0 v p.2 (q,y)|≤P.upper
      rw [abs_of_nonneg (P.lower_pos.le.trans hb.1)]
      exact hb.2
    exact (abs_sub _ _).trans (add_le_add hb hr)
  have hi:=PhysicalInsertion.weighted_generator_integrable c hc ZZ
    (add_nonneg (add_nonneg hκ.le hM) P.upper_nonneg)
    (s:=((carrier (Base p) k).terminal h)) hqp hgap
    hbnd (WordRecursion.hessian G (Mean k 0 q ω h))
  convert! hi.const_mul (1/2:ℝ) using 1
  funext y
  simp only [point,JointPhysicalInsertion.insertion_appendState,WordRecursion.hessian,GaussianTaylor.hessian]
  dsimp only [c,G,ZZ,R,p]
  ring

theorem spatial_split (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ)(q:ℝ≥0)(h:History HeatCircle k)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    (∫y,point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm aU k q h ω y ∂haarAddCircle)=
    (∫y,point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm aV k q h ω y ∂haarAddCircle)+
      Value k 0 q h (fun z=>aU (nativeU ((q,z.1),z.2))-aV (nativeU ((q,z.1),z.2))) ω:=by
  have hU:=point_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm aU haU hbU hages k q h hq ω
  have hV:=point_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm aV haV hbV hages k q h hq ω
  suffices hd:(∫y,point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm aU k q h ω y ∂haarAddCircle)-
      (∫y,point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm aV k q h ω y ∂haarAddCircle)=
      Value k 0 q h (fun z=>aU (nativeU ((q,z.1),z.2))-aV (nativeU ((q,z.1),z.2))) ω by linarith
  rw [←integral_sub hU hV]
  rw [MixedPastNewestError.value,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have hh:=point_split 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q h ω y
  linarith [hh]

/-- The newest discrepancy in the literal ordinary bracket is exactly
the same one-state field whose full collision-simplex L² energy tends
to zero uniformly in the canonical companion index. -/
theorem canonical_spatial_split (D:SmoothApproximation.ScalarData)(j:ℕ)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient j)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ)(q:ℝ≥0)(h:History HeatCircle k)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    (∫y,point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm aU k q h ω y ∂haarAddCircle)=
    (∫y,point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm aV k q h ω y ∂haarAddCircle)+
      Value k 0 q h
        (fun z=>MixedPastNewestIntegratedError.coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j ((q,z.1),z.2)) ω:=by
  have hh:=spatial_split 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages k q h hq ω
  have he:(fun z:Ω×HeatCircle=>aU (nativeU ((q,z.1),z.2))-aV (nativeU ((q,z.1),z.2)))=
      (fun z=>MixedPastNewestIntegratedError.coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j ((q,z.1),z.2)):=by
    funext z
    simp only [MixedPastNewestIntegratedError.coefficientError,hU,hV]
  rw [he] at hh
  exact hh

end SHE.MixedPastNewestOrdinarySplit
