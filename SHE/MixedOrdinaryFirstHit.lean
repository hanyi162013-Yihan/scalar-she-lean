module
public import SHE.MixedOrdinaryKernelMean
public import SHE.OrdinaryUncutSampleExpansion
public import SHE.MixedPastNewestUncutError

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedOrdinaryFirstHit
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

local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)

/-- The positive first-hit error in the actual ordinary-U finite
recursion is precisely the already bounded newest-error primitive.
The companion is matched by its TOTAL coefficient, including kappa. -/
theorem error_mass
    (hP:P.coefficient=fun z=>κ+aV z)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (ν:Measure HeatCircle)(k:ℕ)(ω:Ω):
    OrdinaryUncutSampleExpansion.errorMass modelU (Base (0,pastParameter ω)) ν k ω=
      ∫h,MixedPastNewestOrdinaryError.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k (ω,h) ∂historyMeasure R₀ ν k:=by
  have htotal:(referenceData P P.coefficient haP Λ 0 v b hvb (pastParameter ω)).totalVariance=
      (fun z=>κ+aV z):=hP
  unfold OrdinaryUncutSampleExpansion.errorMass
  rw [htotal,ControlledOrdinaryAverage.measure_eq P P.coefficient haP Λ 0 v b hvb
    ν (pastParameter ω) (0,0) k]
  apply integral_congr_ae
  filter_upwards with h
  exact (MixedPastNewestUncutError.primitive_eq_difference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k (ω,h)).symm

end SHE.MixedOrdinaryFirstHit

