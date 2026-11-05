module
public import SHE.MixedOrdinaryKernelMean
public import SHE.MixedUncutKernelPairing

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedJointKernelMean
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedOrdinaryKernelMean_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedOrdinaryKernelMean_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedOrdinaryKernelMean_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedOrdinaryKernelMean_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedOrdinaryKernelMean_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedOrdinaryKernelMean_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedOrdinaryKernelMean_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedOrdinaryKernelMean_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedOrdinaryKernelMean_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
local notation "modelU"=>MixedNativeOrdinaryModel.model 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)(hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "pastParameter"=>MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

/-- The literal physical joint-current gradient mean is the full theta-one
mean used in the complete native endpoint kernel. -/
theorem mean_one
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    MixedLevelPhysicalGradient.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      (UncutWordEvaluation.normalizedLevel (Base (1,pastParameter ω)) k) (h,(q,ω))=
    MixedPastNativeConsistentPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k 1 q ω h:=by
  change _=MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k 1 q ω h
  rw [MixedPastLiteralMean.meanField_eq_jointMeanVector
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h 1 q hq ω]
  apply PiLp.ext
  intro i
  rw [ControlledJointWeightedWord.jointMeanVector_apply]
  have ho:=ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (1,pastParameter ω) (0,(0,0)) k h
  change PhysicalProfile.physicalHeatMean (embed (S.first q ω))
      ((((carrier (Base (1,pastParameter ω)) k).observations.observations h i).target-(q:ℝ)),
        ((carrier (Base (1,pastParameter ω)) k).observations.observations h i).center)+
    Real.exp (-Λ*(((carrier (Base (1,pastParameter ω)) k).observations.observations h i).stop-(q:ℝ)))*
      PhysicalProfile.physicalHeatMean (embed (S.second q ω-S.first q ω))
        ((((carrier (Base (1,pastParameter ω)) k).observations.observations h i).target-(q:ℝ)),
          ((carrier (Base (1,pastParameter ω)) k).observations.observations h i).center)=_
  rw [ho]
  dsimp only [CoveredControlledLaw.targets,CoveredControlledLaw.centers,StoppedGaussianScore.nativeCenter]
  rw [NativeHeatSpan.scale_inverse]
  ring

end SHE.MixedJointKernelMean

