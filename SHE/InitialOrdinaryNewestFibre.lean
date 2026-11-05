module
public import SHE.InitialOrdinaryNewestFields
public import SHE.InitialNativeKernelFibre
public import SHE.MixedNativePairInitial
public import SHE.MixedPastNewestOriginalMass
public import SHE.PhysicalWordErrorFields
public import SHE.MixedPastNewestOrdinaryError
public import SHE.InitialNativeKernelFields
public import SHE.InitialTerminalFields
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
namespace SHE.InitialOrdinaryNewestFibre
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
attribute [local irreducible] GaussianConvolution.gaussianAverage ActualMeanKernel.cappedAverage
  GaussianTaylor.hessian WordRecursion.hessian UncutSmoothWords.test
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
local notation "Root"=>InitialTerminalLevel.Root R

local notation "Mean"=>InitialNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Error"=>MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "BT" T:max=>InitialNativeKernelFibre.terminal Λ u₀ P haP h T
local notation "NB" T:max=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "K" T:max=>(NB T) (0,(embed u₀,0))
local notation "Lift" T:max=>InitialTerminalFields.lift R T
local notation "MA"=>InitialNativeKernelFibre.actualMean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Point"=>InitialOrdinaryNewestFields.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "CA" T:max=>MixedPastNewestOriginalMass.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "PA" T:max=>MixedPastNewestOriginalMass.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

/-- The full initial Gaussian word, including all baselines, is the
fixed-horizon variable-terminal fibre before taking either derivative. -/
theorem average_fibre(T:Icc (R).base (R).horizon)(k:ℕ)(q:ℝ)(p:History HeatCircle k):
    gaussianAverage (WordRecursion.covariance
      (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 (BT T) bot_le (embed u₀,0)).reference
      ((carrier (K T) k).observations.observations p) q ((carrier (K T) k).terminal p))
        (UncutSmoothWords.test (K T) k p)=
    gaussianAverage (WordRecursion.covariance (R).reference
      ((carrier L k).observations.observations ((Lift T) k p)) q ((carrier L k).terminal ((Lift T) k p)))
        (UncutSmoothWords.test L k ((Lift T) k p)):=by
  have hc:(ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 (BT T) bot_le (embed u₀,0)).reference=(R).reference:=by
    exact (ZeroDirectionProfile.coefficient P Λ 0 0 (embed u₀)).trans
      (ZeroDirectionProfile.coefficient P Λ 0 0 (embed u₀)).symm
  have hterm:=WordRootReindex.terminal L (K T) (InitialTerminalLevel.fibre R T) rfl (fun _=>rfl) k p
  have ho:=WordRootReindex.observations L (K T) (InitialTerminalLevel.fibre R T)
    rfl (fun _=>rfl) (fun _=>rfl) k p
  have ht:=WordRootReindex.test L (K T) (InitialTerminalLevel.fibre R T)
    rfl (fun _=>rfl) (fun _=>rfl) hc rfl (fun _=>rfl) k p
  rw [hc,hterm,ho,ht]
  rfl

theorem terminal_fibre(T:Icc (R).base (R).horizon)(k:ℕ)(p:History HeatCircle k):
    (carrier (K T) k).terminal p=(carrier L k).terminal ((Lift T) k p):=
  WordRootReindex.terminal L (K T) (InitialTerminalLevel.fibre R T) rfl (fun _=>rfl) k p

theorem observations_fibre(T:Icc (R).base (R).horizon)(k:ℕ)(p:History HeatCircle k):
    (carrier (K T) k).observations.observations p=(carrier L k).observations.observations ((Lift T) k p):=
  WordRootReindex.observations L (K T) (InitialTerminalLevel.fibre R T)
    rfl (fun _=>rfl) (fun _=>rfl) k p

/-- The original common initial event is selected BEFORE every terminal,
history and current-time substitution into the initial Gaussian word. -/
theorem current_all_parameters_ae:
    ∀ᵐω∂μ,∀T:Icc (R).base (R).horizon,∀k:ℕ,∀q:ℝ≥0,∀p:History HeatCircle k,
      (CA T) k Error ((q:ℝ),(ω,p))=
        ∫y,Point k q ((Lift T) k p) y ω ∂haarAddCircle:=by
  filter_upwards [MixedNativeAdditiveResidualPair.first_zero 𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S,
    MixedNativeAdditiveResidualPair.second_zero 𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S] with ω hU hV
  intro T k q p
  have hz:(embed (u₀-u₀):CircleL2)=0:=(map_sub embed u₀ u₀).trans (sub_self _)
  have hg:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ 0 (BT T) bot_le
    (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
    (0,(0,0)) (0,(embed u₀,0)) k p
  rw [terminal_fibre Λ u₀ P haP h F hF hFm T k p] at hg
  unfold MixedPastNewestOriginalMass.current MixedPastNewestTimeFields.active
  simp only [Real.toNNReal_coe]
  rw [hg]
  by_cases hq:(q:ℝ)<(carrier L k).terminal ((Lift T) k p)
  · simp only [if_pos hq,InitialOrdinaryNewestFields.point]
    unfold MixedPastNewestError.value
    dsimp only
    simp only [MixedPastJointData.pastU,MixedPastJointData.pastD]
    rw [hU,hV,hz]
    rw [average_fibre Λ u₀ P haP h F hF hFm T k q p]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    rw [observations_fibre Λ u₀ P haP h F hF hFm T k p]
    have hm:=InitialNativeKernelFibre.mean_fibre
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k 0 q T ω p
    let G:=gaussianAverage (WordRecursion.covariance (R).reference
      ((carrier L k).observations.observations ((Lift T) k p)) q ((carrier L k).terminal ((Lift T) k p)))
      (UncutSmoothWords.test L k ((Lift T) k p))
    let E:=heatRow ((carrier L k).observations.observations ((Lift T) k p)) q y
    simp only [ActualMeanKernel.cappedAverage,min_eq_left hq.le]
    convert! congrArg (fun m:WordRecursion.State (1+k)=>Error ((q,ω),y)*WordRecursion.directionalSecond G m E) hm using 1 <;>
      simp only [G,E,WordRecursion.directionalSecond,WordRecursion.hessian]
  · simp only [if_neg hq,InitialOrdinaryNewestFields.point,if_neg hq,integral_zero]

end SHE.InitialOrdinaryNewestFibre
