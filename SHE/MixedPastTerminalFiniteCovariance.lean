module

public import SHE.ControlledFiniteCovarianceFields
public import SHE.MixedPastTerminalPairedFields
public import SHE.JointHistoryFields
public import SHE.WeightedRowTimeShift
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalFiniteCovariance
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

local notation "Cur" => MixedPastTerminalPairedFields.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mark" => ControlledFiniteCovarianceFields.point P haP Λ v b hvb Z htarget hstop F hF hFm

def terminalMean (α:ℝ) (k:ℕ) (h:History X k) (ω:Ω):WordRecursion.State (1+k):=
  (1-α) • Cur false k h ω+α • Cur true k h ω

local notation "Mean" => terminalMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Literal actual finite endpoint covariance interpolation at the original
random terminal frame. The old word keeps its own alpha baseline throughout. -/
def point (k:ℕ) (α θ₀ θ₁ ζ:ℝ) (h:History X k) (ω:Ω):ℝ:=
  Mark (α,(U ω,Dir ω)) k h ((carrier Zero k).terminal h) θ₀ θ₁ ζ (Mean α k h ω)

attribute [local irreducible] MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse ControlledFamilyProfileForest.oldProfile PhysicalChainArrays.oldAverage MixedPastTerminalPairedFields.current
set_option backward.isDefEq.respectTransparency true

local notation "Point" => point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Joint Borel dependence before any newest-space or interpolation
section is chosen. All current and past variables are genuinely dependent. -/
theorem point_variable_measurable {W:Type} [MeasurableSpace W] (k:ℕ)
    (h:W→History X k) (hh:Measurable h) (ω:W→Ω) (hω:Measurable ω)
    (α θ₀ θ₁ ζ:W→ℝ) (hα:Measurable α) (hθ₀:Measurable θ₀)
    (hθ₁:Measurable θ₁) (hζ:Measurable ζ):
    Measurable (fun w=>Point k (α w) (θ₀ w) (θ₁ w) (ζ w) (h w) (ω w)):=by
  have hu:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:Measurable Dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hp:Measurable (fun w=>(α w,(U (ω w),Dir (ω w)))):=
    hα.prodMk ((hu.comp hω).prodMk (hd.comp hω))
  have hcur₀:Measurable (fun w=>Cur false k (h w) (ω w)):=
    (MixedPastTerminalPairedFields.current_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm false k).comp (hh.prodMk hω)
  have hcur₁:Measurable (fun w=>Cur true k (h w) (ω w)):=
    (MixedPastTerminalPairedFields.current_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm true k).comp (hh.prodMk hω)
  have hm:Measurable (fun w=>Mean (α w) k (h w) (ω w)):=
    ((measurable_const.sub hα).smul hcur₀).add (hα.smul hcur₁)
  have ht:Measurable (fun w=>(carrier Zero k).terminal (h w)):=
    (carrier Zero k).terminal_measurable.comp hh
  exact ControlledFiniteCovarianceFields.point_variable_measurable P haP Λ v b hvb Z htarget hstop F hF hFm k
    _ hp h hh _ θ₀ θ₁ ζ ht hθ₀ hθ₁ hζ _ hm

/-- The actual moment event is measurable over original histories;
this permits genuine newest-coordinate Fubini. -/
theorem moment_measurable (k:ℕ) (α θ₀ θ₁ ζ:ℝ) (p:ℕ):
    Measurable (fun h:History X k=>∫⁻ω,ENNReal.ofReal
      (|Point k α θ₀ θ₁ ζ h ω|^(2*p)) ∂μ):=by
  have hp:Measurable (fun z:History X k×Ω=>Point k α θ₀ θ₁ ζ z.1 z.2):=
    point_variable_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k Prod.fst measurable_fst Prod.snd measurable_snd
      _ _ _ _ measurable_const measurable_const measurable_const measurable_const
  have hm:Measurable (fun z:History X k×Ω=>ENNReal.ofReal
      (|Point k α θ₀ θ₁ ζ z.1 z.2|^(2*p))):=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp hp).pow_const (2*p))
  exact hm.lintegral_prod_right


end SHE.MixedPastTerminalFiniteCovariance
