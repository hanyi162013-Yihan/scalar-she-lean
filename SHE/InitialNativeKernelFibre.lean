module
public import SHE.InitialNativeKernelFields
public import SHE.ControlledScalarReference
public import SHE.WordRootState
public import SHE.MovingNativeFields
public import SHE.ZeroDirectionProfile
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.InitialNativeKernelFibre
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeKernelFields_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeKernelFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeKernelFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeKernelFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeKernelFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeKernelFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance movingNativeKernelFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeKernelFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativeKernelFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeKernelFields_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "L"=>InitialTerminalLevel.level R F hF hFm
abbrev terminal (T:Icc (R).base (R).horizon):ℝ≥0:=⟨T.1,T.2.1⟩
local notation "BT" T:max=>terminal Λ u₀ P haP h T
local notation "NB" T:max=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Zero" T:max=>(NB T) (0,(0,0))
local notation "Lift" T:max=>InitialTerminalFields.lift R T
local notation "Mean"=>InitialNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
abbrev actualMean (k:ℕ)(θ:ℝ)(q:ℝ≥0)(T:Icc (R).base (R).horizon)(ω:Ω):History HeatCircle k→WordRecursion.State (1+k):=
  MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP 0 (BT T) bot_le
    (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k θ q ω
local notation "MA"=>actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

private theorem root_lift (T:Icc (R).base (R).horizon)(k:ℕ)(p:History HeatCircle k):
    rootParameter k ((Lift T) k p)=(T,rootParameter k p):=by
  induction k with
  | zero=>rfl
  | succ k ih=>exact ih p.1

/-- The fixed-horizon variable-root current is the literal initial-past current, with full covered stops. -/
theorem mean_fibre (k:ℕ)(θ:ℝ)(q:ℝ≥0)(T:Icc (R).base (R).horizon)(ω:Ω)(p:History HeatCircle k):
    MA k θ q T ω p=Mean k θ q ω ((Lift T) k p):=by
  have ho:=WordRootReindex.observations L (Zero T) (InitialTerminalLevel.fibre R T)
    rfl (fun _=>rfl) (fun _=>rfl) k p
  have hi:initialTerminal L k ((Lift T) k p)=(T:ℝ):=by
    unfold initialTerminal
    rw [root_lift]
    rfl
  have hz:initialTerminal (Zero T) k p=(T:ℝ):=rfl
  have hs:stops (Zero T) k p=stops L k ((Lift T) k p):=by
    unfold stops
    rw [ho,hz,hi]
    rfl
  have ht:targets (Zero T) k p=targets L k ((Lift T) k p):=by
    unfold targets
    rw [ho]
    rfl
  have hx:centers (Zero T) k p=centers L k ((Lift T) k p):=by
    unfold centers
    rw [ho]
    rfl
  unfold actualMean MixedPastLiteralPoint.meanField MixedPastJointData.mean MixedNativePastThetaCentering.current
    InitialNativeKernelFields.mean
  apply PiLp.ext
  intro i
  simp only [WithLp.ofLp_toLp,NNReal.coe_zero,sub_zero,add_zero]
  rw [hs,ht,hx]

/-- Native initial kernels at fixed deterministic data; actual random initial data agree on the common initial event. -/
def deterministicPoint (k:ℕ)(weighted:Bool)(θ:ℝ)(q:ℝ≥0)(T:Icc (R).base (R).horizon)
    (p:History HeatCircle k)(y:HeatCircle)(ω:Ω):ℝ:=
  if weighted then ActualMeanKernel.weightedPoint ((NB T) (θ,(embed u₀,0))) k Λ q q (MA k θ q T ω) p y
  else ActualMeanKernel.rowPoint ((NB T) (θ,(embed u₀,0))) k q q (MA k θ q T ω) p y
local notation "DP"=>deterministicPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem point_fibre (k:ℕ)(weighted:Bool)(θ:ℝ)(q:ℝ≥0)(T:Icc (R).base (R).horizon)
    (p:History HeatCircle k)(y:HeatCircle)(ω:Ω):
    DP k weighted θ q T p y ω=InitialNativeKernelFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h F hF hFm k weighted θ q T p y ω:=by
  let K:=(NB T) (θ,(embed u₀,0))
  have hc:(ControlledReferenceLevel.referenceData P P.coefficient haP Λ θ 0 (BT T) bot_le (embed u₀,0)).reference=(R).reference:=by
    exact (ZeroDirectionProfile.coefficient P Λ θ 0 (embed u₀)).trans
      (ZeroDirectionProfile.coefficient P Λ 0 0 (embed u₀)).symm
  have hterm:=WordRootReindex.terminal L K (InitialTerminalLevel.fibre R T) rfl (fun _=>rfl) k p
  have ho:=WordRootReindex.observations L K (InitialTerminalLevel.fibre R T)
    rfl (fun _=>rfl) (fun _=>rfl) k p
  have ht:=WordRootReindex.test L K (InitialTerminalLevel.fibre R T)
    rfl (fun _=>rfl) (fun _=>rfl) hc rfl (fun _=>rfl) k p
  have hm:=mean_fibre 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k θ q T ω p
  unfold deterministicPoint InitialNativeKernelFields.point
  change (if weighted then ActualMeanKernel.weightedPoint K k Λ q q (MA k θ q T ω) p y else
    ActualMeanKernel.rowPoint K k q q (MA k θ q T ω) p y)=_
  cases weighted
  · simp only [Bool.false_eq_true,if_false]
    unfold ActualMeanKernel.rowPoint
    rw [hterm,ho,hc,ht,hm]
    rfl
  · simp only [if_true]
    unfold ActualMeanKernel.weightedPoint
    rw [hterm,ho,hc,ht,hm]
    rfl

end SHE.InitialNativeKernelFibre
