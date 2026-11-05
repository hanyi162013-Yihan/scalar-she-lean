module
public import SHE.MixedPastNewestCollision
public import SHE.MixedPastLiteralFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestFields
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestFields_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestFields_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestFields_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestFields_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestFields_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestFields_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestFields_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestFields_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestFields_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type}[MeasurableSpace Ω]{X:Type}[MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def active (k:ℕ)(θ:ℝ)(q:ℝ≥0)(e:Ω×HeatCircle→ℝ)(z:Ω×History X k):ℝ:=
  if (q:ℝ)<(carrier Zero k).terminal z.2 then Value k θ q z.2 e z.1 else 0

attribute [local irreducible] active MixedPastLiteralPoint.meanField MixedPastJointData.pastU
  MixedPastJointData.pastD ActualMeanKernel.cappedAverage GaussianTaylor.hessian

/-- Genuine joint sample/history Borel field of the newest error, before
any old-space or time averaging. The multiplier remains outside the Gaussian. -/
theorem active_measurable (k:ℕ)(θ:ℝ)(q:ℝ≥0)(e:Ω×HeatCircle→ℝ)(he:Measurable e):
    Measurable (active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q e):=by
  let W:=Ω×History X k
  let p:W→ℝ×Inputs:=fun z=>(θ,(MixedPastJointData.pastU
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1,
      MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1))
  let m:W→WordRecursion.State (1+k):=fun z=>MixedPastLiteralPoint.meanField
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
      k θ q z.1 z.2
  have hu:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hp:Measurable p:=measurable_const.prodMk
    ((hu.comp measurable_fst).prodMk (hd.comp measurable_fst))
  have hm:Measurable m:=MixedPastLiteralFields.meanField_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q
  let B:W→WordRecursion.State (1+k)→L[ℝ] WordRecursion.State (1+k)→L[ℝ]ℝ:=fun z=>
    GaussianTaylor.hessian (ActualMeanKernel.cappedAverage (Base (p z)) k q z.2) (m z)
  have hmap:Measurable (fun z:W=>((p z,((q:ℝ),z.2)),m z)):=
    (hp.prodMk (measurable_const.prodMk measurable_snd)).prodMk hm
  have hB0:=(ControlledThetaBackwardFields.hessian_joint_measurable
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k).comp hmap
  have hB:Measurable B:=hB0
  let row:W×HeatCircle→WordRecursion.State (1+k):=fun z=>
    heatRow ((carrier Zero k).observations.observations z.1.2) q z.2
  have hrmap:Measurable (fun z:W×HeatCircle=>(z.1.2,((q:ℝ),z.2))):=
    measurable_fst.snd.prodMk (measurable_const.prodMk measurable_snd)
  have hr0:=(carrier Zero k).observations.heatRow_measurable.comp hrmap
  have hr:Measurable row:=hr0
  have hbil:Measurable (fun z:W×HeatCircle=>B z.1 (row z) (row z)):=
    ((continuous_fst.clm_apply continuous_snd).measurable.comp
      (((continuous_fst.clm_apply continuous_snd).measurable.comp
        ((hB.comp measurable_fst).prodMk hr)).prodMk hr))
  have hs:MeasurableSet {z:W×HeatCircle|(q:ℝ)<(carrier Zero k).terminal z.1.2}:=
    measurableSet_lt measurable_const ((carrier Zero k).terminal_measurable.comp measurable_fst.snd)
  let f:W×HeatCircle→ℝ:=fun z=>if (q:ℝ)<(carrier Zero k).terminal z.1.2 then
    (1/2:ℝ)*(e (z.1.1,z.2)*B z.1 (row z) (row z)) else 0
  have hf:Measurable f:=((he.comp (measurable_fst.fst.prodMk measurable_snd)).mul hbil |>.const_mul (1/2:ℝ)).ite hs measurable_const
  have hh:=(hf.stronglyMeasurable.integral_prod_right' (ν:=haarAddCircle)).measurable
  convert! hh using 1
  funext z
  unfold active
  by_cases hq:(q:ℝ)<(carrier Zero k).terminal z.2
  · simp only [if_pos hq]
    unfold MixedPastNewestError.value
    have hterm:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (p z) (0,(0,0)) k z.2
    have hqt:(q:ℝ)≤(carrier (Base (p z)) k).terminal z.2:=by rw [hterm];exact hq.le
    have hobs:=ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (p z) (0,(0,0)) k z.2
    dsimp only [f]
    simp only [if_pos hq,integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [B,row,m]
    rw [hobs]
    simp only [ActualMeanKernel.cappedAverage,min_eq_left hqt,WordRecursion.directionalSecond,
      WordRecursion.hessian,GaussianTaylor.hessian]
    simp only [hobs]
    rfl
  · simp only [f,if_neg hq,integral_zero]

end SHE.MixedPastNewestFields
