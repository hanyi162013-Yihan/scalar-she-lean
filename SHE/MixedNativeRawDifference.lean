module
public import SHE.MixedOrdinaryNativePairing
public import SHE.MixedJointNativePairing
public import SHE.MixedPastNativeKernel

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedNativeRawDifference
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

local notation "NL"=>(fun θ p k=>UncutWordEvaluation.normalizedLevel (Base (θ,p)) k)
local notation "Mean₀"=>(fun k h (q:ℝ≥0) ω=>OrdinaryPhysicalGradient.mean modelU (NL 0 (pastParameter ω) k) (h,(q,ω)))
local notation "Mean₁"=>(fun k h (q:ℝ≥0) ω=>MixedLevelPhysicalGradient.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (NL 1 (pastParameter ω) k) (h,(q,ω)))
local notation "D₀"=>(fun k h (q:ℝ≥0) ω=>fderiv ℝ (GaussianConvolution.gaussianAverage
  (covariance (referenceData P P.coefficient haP Λ 0 v b hvb (pastParameter ω)).reference
    ((NL 0 (pastParameter ω) k).observations.observations h) (q:ℝ) ((NL 0 (pastParameter ω) k).terminal h))
  (UncutSmoothWords.test (Base (0,pastParameter ω)) k h)) (Mean₀ k h q ω))
local notation "D₁"=>(fun k h (q:ℝ≥0) ω=>fderiv ℝ (GaussianConvolution.gaussianAverage
  (covariance (referenceData P P.coefficient haP Λ 1 v b hvb (pastParameter ω)).reference
    ((NL 1 (pastParameter ω) k).observations.observations h) (q:ℝ) ((NL 1 (pastParameter ω) k).terminal h))
  (UncutSmoothWords.test (Base (1,pastParameter ω)) k h)) (Mean₁ k h q ω))

def kernel(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω):CircleL2:=
  FiniteHeatRows.kernel (D₁ k h q ω) ((NL 1 (pastParameter ω) k).observations.observations h) q-
  FiniteHeatRows.kernel (D₀ k h q ω) ((NL 0 (pastParameter ω) k).observations.observations h) q

def weightedKernel(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω):CircleL2:=
  StopWeightedRows.kernel (D₁ k h q ω) Λ ((NL 1 (pastParameter ω) k).observations.observations h) q q

local notation "K"=>kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P haP v b hvb Z htarget hstop F hF hFm
local notation "KW"=>weightedKernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- The paired raw input is EXACTLY the complete endpoint-difference
kernel on the common additive/U factors, plus the true theta-one stopped
kernel acting on the matched Haar V-minus-U column. -/
theorem channels(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω)
    (hvq:(v:ℝ)<(q:ℝ))(hqt:(q:ℝ)<(carrier Zero k).terminal h)(j:HaarNode):
    let joint:=MixedUncutPhysicalGradient.raw
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (Base (1,pastParameter ω)) k (h,(q,ω))
    let ordinary:=OrdinaryUncutPhysicalGradient.raw modelU (Base (0,pastParameter ω)) k (h,(q,ω))
    let col₀:=CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)
    let colU:=CircleNormalization.push (globalHaarColumn j (ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,ω)).1)
    let colV:=CircleNormalization.push (globalHaarColumn j (ContinuousHeatMild.coefficientFunction haV hell hbV S.second (q,ω)).1)
    NativeJointColumnDirections.left j (joint-ordinary)=(inner ℂ (K k h q ω) col₀).re∧
    NativeJointColumnDirections.right j (joint-ordinary)=(inner ℂ (K k h q ω) colU).re+
      (inner ℂ (KW k h q ω) (colV-colU)).re:=by
  intro joint ordinary col₀ colU colV
  have ht(θ:ℝ):(q:ℝ)<(NL θ (pastParameter ω) k).terminal h:=by
    change (q:ℝ)<(carrier (Base (θ,pastParameter ω)) k).terminal h
    rwa [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (θ,pastParameter ω) (0,(0,0)) k h]
  have hT(θ:ℝ)(i:Fin (1+k)):(q:ℝ)<((NL θ (pastParameter ω) k).observations.observations h i).target:=
    (ht θ).trans_le ((NL θ (pastParameter ω) k).targets_after h i)
  obtain ⟨hl₁,hr₁⟩:=MixedUncutKernelPairing.channels
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (Base (1,pastParameter ω)) k (h,(q,ω)) ⟨hvq,ht 1⟩ (hT 1) j
  obtain ⟨hl₀,hr₀⟩:=OrdinaryUncutPhysicalColumns.channels modelU (Base (0,pastParameter ω)) k
    (h,(q,ω)) ⟨hvq,ht 0⟩ (hT 0) j
  constructor
  · rw [map_sub,hl₁,hl₀]
    change (inner ℂ _ col₀).re-(inner ℂ _ col₀).re=(inner ℂ (_-_) col₀).re
    rw [inner_sub_left,Complex.sub_re]
  · rw [map_sub,hr₁,hr₀]
    change (inner ℂ _ colU).re+(inner ℂ _ (colV-colU)).re-(inner ℂ _ colU).re=
      (inner ℂ (_-_) colU).re+(inner ℂ _ (colV-colU)).re
    rw [inner_sub_left,Complex.sub_re]
    dsimp only [weightedKernel,StopWeightedRows.kernel]
    ring

/-- On native Haar space the genuine paired common-factor kernel is the
literal complete point difference, with both entire Gaussian endpoints. -/
theorem kernel_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    (K k h q ω:HeatCircle→ℂ)=ᵐ[AddCircle.haarAddCircle] fun y=>
      (MixedPastNativeKernel.difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k q q h y ω:ℂ):=by
  have hj:=MixedJointNativePairing.kernel_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω
  have hu:=MixedOrdinaryNativePairing.kernel_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω
  have hs:=Lp.coeFn_sub
    (FiniteHeatRows.kernel (D₁ k h q ω) ((NL 1 (pastParameter ω) k).observations.observations h) q)
    (FiniteHeatRows.kernel (D₀ k h q ω) ((NL 0 (pastParameter ω) k).observations.observations h) q)
  filter_upwards [hj,hu,hs] with y hyj hyu hys
  change (_-_:CircleL2) y=_
  rw [hys]
  change (FiniteHeatRows.kernel (D₁ k h q ω) ((NL 1 (pastParameter ω) k).observations.observations h) q) y-
    (FiniteHeatRows.kernel (D₀ k h q ω) ((NL 0 (pastParameter ω) k).observations.observations h) q) y=_
  rw [hyj,hyu]
  simp only [MixedPastNativeKernel.difference,Complex.ofReal_sub]

/-- The signed matched noise factor keeps the literal theta-one
stop-weighted endpoint, with covariance/current mean still at q. -/
theorem weighted_kernel_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω):
    (KW k h q ω:HeatCircle→ℂ)=ᵐ[AddCircle.haarAddCircle] fun y=>
      (MixedPastLiteralPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 1 q q h y ω:ℂ):=
  MixedJointNativePairing.weighted_kernel_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω

/-- The common-factor derivative is paired with the true signed native
input before any spatial or old-time averaging. -/
theorem functional
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω)(f:CircleL2):
    inner ℂ (K k h q ω) f=∫y:HeatCircle,
      (MixedPastNativeKernel.difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k q q h y ω:ℂ)*f y ∂AddCircle.haarAddCircle:=by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernel_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω] with y hy
  rw [hy]
  simp only [RCLike.inner_apply,Complex.conj_ofReal]
  ring

theorem weighted_functional
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)
    (hq:(q:ℝ)<(carrier Zero k).terminal h)(ω:Ω)(f:CircleL2):
    inner ℂ (KW k h q ω) f=∫y:HeatCircle,
      (MixedPastLiteralPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 1 q q h y ω:ℂ)*f y ∂AddCircle.haarAddCircle:=by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weighted_kernel_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h q hq ω] with y hy
  rw [hy]
  simp only [RCLike.inner_apply,Complex.conj_ofReal]
  ring

end SHE.MixedNativeRawDifference

