module
public import SHE.MixedNativeRawDifference

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedNativeRawSupport
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

/-- Both independently constructed raw inputs have the same genuine
open current window. This whole-vector support precedes all coordinates,
old-space averaging and any canonical-coefficient specialization. -/
theorem off_active(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω)
    (hq:¬((v:ℝ)<(q:ℝ)∧(q:ℝ)<(carrier Zero k).terminal h)):
    Joint k h q ω-Ordinary k h q ω=0:=by
  have ht(θ:ℝ):(UncutWordEvaluation.normalizedLevel (Base (θ,pastParameter ω)) k).terminal h=
      (carrier Zero k).terminal h:=
    ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (θ,pastParameter ω) (0,(0,0)) k h
  have hn(θ:ℝ):¬((referenceData P P.coefficient haP Λ θ v b hvb (pastParameter ω)).base<(q:ℝ)∧
      (q:ℝ)<(UncutWordEvaluation.normalizedLevel (Base (θ,pastParameter ω)) k).terminal h):=by
    change ¬((v:ℝ)<(q:ℝ)∧_)
    rwa [ht θ]
  simp only [MixedUncutPhysicalGradient.raw,MixedLevelPhysicalGradient.raw,if_neg (hn 1),
    OrdinaryUncutPhysicalGradient.raw,OrdinaryPhysicalGradient.raw,if_neg (hn 0),
    smul_zero,sub_zero]

theorem coordinate_off_active(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω)
    (hq:¬((v:ℝ)<(q:ℝ)∧(q:ℝ)<(carrier Zero k).terminal h))
    (ℓ:Both RealHaarInput→L[ℝ]ℝ):
    ℓ (Joint k h q ω)-ℓ (Ordinary k h q ω)=0:=by
  rw [←map_sub,off_active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP v b hvb Z htarget hstop F hF hFm k h q ω hq,map_zero]

/-- The actual unweighted endpoint point is zero after the terminal,
independently of the moving Gaussian law and every current sample. -/
theorem point_off_terminal(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω)(θ:ℝ)(y:HeatCircle)
    (hq:¬(q:ℝ)<(carrier Zero k).terminal h):
    MixedPastNativeConsistentPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q q h y ω=0:=by
  have ht:(carrier (Base (θ,pastParameter ω)) k).terminal h=(carrier Zero k).terminal h:=
    ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (θ,pastParameter ω) (0,(0,0)) k h
  have hn:¬((q:ℝ)<(carrier (Base (θ,pastParameter ω)) k).terminal h∧
      (q:ℝ)<(carrier (Base (θ,pastParameter ω)) k).terminal h):=by
    rw [ht]
    exact fun h=>hq h.1
  unfold MixedPastNativeConsistentPoint.point
  change ActualMeanKernel.rowPoint (Base (θ,pastParameter ω)) k q q _ h y=0
  rw [ActualMeanKernel.rowPoint,if_neg hn]

theorem weighted_point_off_terminal(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω)(θ:ℝ)(y:HeatCircle)
    (hq:¬(q:ℝ)<(carrier Zero k).terminal h):
    MixedPastLiteralPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q q h y ω=0:=by
  have ht:(carrier (Base (θ,pastParameter ω)) k).terminal h=(carrier Zero k).terminal h:=
    ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (θ,pastParameter ω) (0,(0,0)) k h
  have hn:¬((q:ℝ)<(carrier (Base (θ,pastParameter ω)) k).terminal h∧
      (q:ℝ)<(carrier (Base (θ,pastParameter ω)) k).terminal h):=by
    rw [ht]
    exact fun h=>hq h.1
  unfold MixedPastLiteralPoint.point
  change ActualMeanKernel.weightedPoint (Base (θ,pastParameter ω)) k Λ q q _ h y=0
  rw [ActualMeanKernel.weightedPoint,if_neg hn]

theorem difference_off_terminal(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω)(y:HeatCircle)
    (hq:¬(q:ℝ)<(carrier Zero k).terminal h):
    MixedPastNativeKernel.difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q q h y ω=0:=by
  rw [MixedPastNativeKernel.difference,
    point_off_terminal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k h q ω 1 y hq,
    point_off_terminal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k h q ω 0 y hq,sub_self]

end SHE.MixedNativeRawSupport

