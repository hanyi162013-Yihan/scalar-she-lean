module
public import SHE.MixedNativeRawSupport

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedNativeRawActions
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

local notation "Joint"=>(fun k h q ω=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (Base (1,pastParameter ω)) k (h,(q,ω)))
local notation "Ordinary"=>(fun k h q ω=>OrdinaryUncutPhysicalGradient.raw modelU
  (Base (0,pastParameter ω)) k (h,(q,ω)))
local notation "Diff"=>MixedPastNativeKernel.difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Weighted"=>MixedPastLiteralPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- Literal paired original raw actions on EVERY history after v.
Inactive terminal histories vanish on both sides; the common channels
use the complete point difference and the signed channel the actual
theta-one stopped row, with all original targets/stops retained. -/
theorem channels
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω)(hvq:(v:ℝ)<(q:ℝ))(j:HaarNode):
    let col₀:=CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)
    let colU:=CircleNormalization.push (globalHaarColumn j (ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,ω)).1)
    let colV:=CircleNormalization.push (globalHaarColumn j (ContinuousHeatMild.coefficientFunction haV hell hbV S.second (q,ω)).1)
    NativeJointColumnDirections.left j (Joint k h q ω-Ordinary k h q ω)=
      (∫y:HeatCircle,(Diff k q q h y ω:ℂ)*col₀ y ∂AddCircle.haarAddCircle).re∧
    NativeJointColumnDirections.right j (Joint k h q ω-Ordinary k h q ω)=
      (∫y:HeatCircle,(Diff k q q h y ω:ℂ)*colU y ∂AddCircle.haarAddCircle).re+
      (∫y:HeatCircle,(Weighted k 1 q q h y ω:ℂ)*(colV-colU) y ∂AddCircle.haarAddCircle).re:=by
  intro col₀ colU colV
  by_cases hqt:(q:ℝ)<(carrier Zero k).terminal h
  · obtain ⟨hl,hr⟩:=MixedNativeRawDifference.channels
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z htarget hstop F hF hFm k h q ω hvq hqt j
    rw [MixedNativeRawDifference.functional
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hqt ω col₀] at hl
    rw [MixedNativeRawDifference.functional
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hqt ω colU,
      MixedNativeRawDifference.weighted_functional
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hqt ω (colV-colU)] at hr
    exact ⟨hl,hr⟩
  · have hz:Joint k h q ω-Ordinary k h q ω=0:=
      MixedNativeRawSupport.off_active
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P haP v b hvb Z htarget hstop F hF hFm k h q ω (fun h=>hqt h.2)
    have hd(y:HeatCircle):Diff k q q h y ω=0:=
      MixedNativeRawSupport.difference_off_terminal
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k h q ω y hqt
    have hw(y:HeatCircle):Weighted k 1 q q h y ω=0:=
      MixedNativeRawSupport.weighted_point_off_terminal
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k h q ω 1 y hqt
    rw [hz]
    simp [hd,hw]
    
end SHE.MixedNativeRawActions

