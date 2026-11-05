module
public import SHE.MixedJointKernelMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedJointNativePairing
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

local notation "Point"=>MixedPastNativeConsistentPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "NL"=>(fun p k=>UncutWordEvaluation.normalizedLevel (Base p) k)
local notation "Mean"=>(fun k h (q:ℝ≥0) ω=>MixedLevelPhysicalGradient.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (NL (1,pastParameter ω) k) (h,(q,ω)))
local notation "D"=>(fun k h (q:ℝ≥0) ω=>fderiv ℝ (GaussianConvolution.gaussianAverage
  (covariance (referenceData P P.coefficient haP Λ 1 v b hvb (pastParameter ω)).reference
    ((NL (1,pastParameter ω) k).observations.observations h) (q:ℝ) ((NL (1,pastParameter ω) k).terminal h))
  (UncutSmoothWords.test (Base (1,pastParameter ω)) k h)) (Mean k h q ω))

/-- The native L2 derivative kernel of the actual joint theta-one input is the
literal theta-one endpoint kernel used in the complete comparison. -/
theorem kernel_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    (FiniteHeatRows.kernel (D k h q ω) ((NL (1,pastParameter ω) k).observations.observations h) q:HeatCircle→ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun y=>(Point k 1 q q h y ω:ℂ):=by
  have ht:(q:ℝ)<(carrier (Base (1,pastParameter ω)) k).terminal h:=by
    rwa [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (1,pastParameter ω) (0,(0,0)) k h]
  have hT(i:Fin (1+k)):(q:ℝ)<((NL (1,pastParameter ω) k).observations.observations h i).target:=
    ht.trans_le ((NL (1,pastParameter ω) k).targets_after h i)
  filter_upwards [FiniteHeatRows.kernel_ae (D k h q ω)
    ((NL (1,pastParameter ω) k).observations.observations h) hT] with y hy
  rw [hy]
  unfold MixedPastNativeConsistentPoint.point
  change _=(ActualMeanKernel.rowPoint (Base (1,pastParameter ω)) k q q
    (MixedPastNativeConsistentPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k 1 q ω) h y:ℂ)
  rw [ActualMeanKernel.rowPoint_of_active _ _ _ _ _ _ _ ht ht]
  rw [←MixedJointKernelMean.mean_one 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω]
  rfl

/-- Exact signed native pairing with the complete joint endpoint
kernel. No modulus or surrogate input is introduced. -/
theorem functional
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω)(f:CircleL2):
    FiniteHeatRows.functional (D k h q ω) ((NL (1,pastParameter ω) k).observations.observations h) q f=
      ∫y:HeatCircle,(Point k 1 q q h y ω:ℂ)*f y ∂AddCircle.haarAddCircle:=by
  change inner ℂ (FiniteHeatRows.kernel _ _ _) f=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernel_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω] with y hy
  rw [hy]
  simp only [RCLike.inner_apply,Complex.conj_ofReal]
  ring



local notation "Weighted"=>MixedPastLiteralPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- The actual stopped signed channel retains its full q-law and the
original stop-dependent weights inside the native kernel. -/
theorem weighted_kernel_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    (StopWeightedRows.kernel (D k h q ω) Λ ((NL (1,pastParameter ω) k).observations.observations h) q q:HeatCircle→ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun y=>(Weighted k 1 q q h y ω:ℂ):=by
  have ht:(q:ℝ)<(carrier (Base (1,pastParameter ω)) k).terminal h:=by
    rwa [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (1,pastParameter ω) (0,(0,0)) k h]
  have hT(i:Fin (1+k)):(q:ℝ)<((NL (1,pastParameter ω) k).observations.observations h i).target:=
    ht.trans_le ((NL (1,pastParameter ω) k).targets_after h i)
  filter_upwards [StopWeightedRows.kernel_ae (D k h q ω) Λ
    ((NL (1,pastParameter ω) k).observations.observations h) q q hT] with y hy
  rw [hy]
  unfold MixedPastLiteralPoint.point
  change _=(ActualMeanKernel.weightedPoint (Base (1,pastParameter ω)) k Λ q q
    (MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k 1 q ω) h y:ℂ)
  rw [ActualMeanKernel.weightedPoint_of_active _ _ _ _ _ _ _ _ ht ht]
  have hm:=MixedJointKernelMean.mean_one 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω
  change _=MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k 1 q ω h at hm
  rw [←hm]
  rfl

theorem weighted_functional
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω)(f:CircleL2):
    FiniteHeatRows.functional ((D k h q ω).comp
      (StopWeightedRows.diagonal (StopWeightedRows.weights Λ
        ((NL (1,pastParameter ω) k).observations.observations h) q)))
      ((NL (1,pastParameter ω) k).observations.observations h) q f=
      ∫y:HeatCircle,(Weighted k 1 q q h y ω:ℂ)*f y ∂AddCircle.haarAddCircle:=by
  change inner ℂ (StopWeightedRows.kernel _ _ _ _ _) f=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weighted_kernel_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω] with y hy
  rw [hy]
  simp only [RCLike.inner_apply,Complex.conj_ofReal]
  ring

end SHE.MixedJointNativePairing

