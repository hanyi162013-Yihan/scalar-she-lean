module

public import SHE.ControlledFiniteCovarianceMass
public import SHE.MixedPastTerminalFiniteCovariance
public import SHE.StrictHistoryFields
public import SHE.ParentMeanDensity
public import SHE.PastWordTimeFields
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

namespace SHE.MixedPastTerminalCovarianceFields
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

open Classical

local notation "Point"=>MixedPastTerminalFiniteCovariance.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

def mass (k:ℕ) (ζ:ℝ) (h:History X k) (ω:Ω):ℝ:=
  ControlledFiniteCovarianceMass.mass P haP Λ v b hvb Z htarget hstop F hF hFm
    (1,(U ω,Dir ω)) k h ((carrier Zero k).terminal h) 0 1 ζ

local notation "Mass"=>mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The genuine recursive terminal covariance field uses the original
strict-history guard; no assertion about vanishing individual assignments
outside that region is used. -/
def active (k:ℕ) (ζ:ℝ) (h:History X k) (ω:Ω):ℝ:=
  if StrictHistory Zero k h then Point k 1 0 1 ζ h ω else 0

local notation "Active"=>active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Joint Borel ORIGINAL mass before all sample/history sections. -/
theorem mass_measurable (k:ℕ) (ζ:ℝ):
    Measurable (fun z:History X k×Ω=>Mass k ζ z.1 z.2):=by
  have hu:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:Measurable Dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hp:Measurable (fun z:History X k×Ω=>((1:ℝ),(U z.2,Dir z.2))):=
    measurable_const.prodMk ((hu.comp measurable_snd).prodMk (hd.comp measurable_snd))
  exact ControlledFiniteCovarianceMass.mass_variable_measurable P haP Λ v b hvb Z htarget hstop F hF hFm k
    _ hp Prod.fst measurable_fst _ _ _ _ ((carrier Zero k).terminal_measurable.comp measurable_fst)
    measurable_const measurable_const measurable_const

theorem mass_moment_measurable (k:ℕ) (ζ:ℝ) (p:ℕ):
    Measurable (fun h:History X k=>∫ω,(Mass k ζ h ω)^(2*p) ∂μ):=by
  have hm:Measurable (fun z:History X k×Ω=>(Mass k ζ z.1 z.2)^(2*p)):=
    (mass_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k ζ).pow_const _
  exact (hm.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable

theorem active_measurable (k:ℕ) (ζ:ℝ):
    Measurable (fun z:History X k×Ω=>Active k ζ z.1 z.2):=by
  have hp:Measurable (fun z:History X k×Ω=>Point k 1 0 1 ζ z.1 z.2):=
    MixedPastTerminalFiniteCovariance.point_variable_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k
    Prod.fst measurable_fst Prod.snd measurable_snd (fun _=>1) (fun _=>0) (fun _=>1) (fun _=>ζ)
    measurable_const measurable_const measurable_const measurable_const
  exact hp.ite ((strictHistory_measurableSet Zero k).preimage measurable_fst) measurable_const

/-- Deterministic old forest and all-assignment scale. The absolute value
only extends the bound Borelly off the strict original history region. -/
def amplitude (k:ℕ) (h:History X k) (A0 ν:ℝ):ℝ:=
  |timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k h*
    ParentMeanDensity.parentProduct Zero k h| *PastWordTimeFields.total Zero P k h A0 ν/2

local notation "Amp"=>amplitude Λ P haP v b hvb Z htarget hstop F hF hFm

theorem amplitude_measurable (k:ℕ) (A0 ν:ℝ):Measurable (fun h:History X k=>Amp k h A0 ν):=by
  exact (((continuous_abs.measurable.comp
    ((FixedHistoryTimeFactors.timeWeight_measurable Zero _ _ k).mul
      (ParentMeanDensity.parentProduct_measurable Zero k))).mul
      (PastWordTimeFields.total_measurable Zero P k A0 ν)).div_const 2)

theorem amplitude_nonneg (k:ℕ) (h:History X k) (A0 ν:ℝ):0≤Amp k h A0 ν:=
  div_nonneg (mul_nonneg (abs_nonneg _) (PastWordTimeFields.total_nonneg Zero P k h A0 ν)) (by norm_num)

end SHE.MixedPastTerminalCovarianceFields
