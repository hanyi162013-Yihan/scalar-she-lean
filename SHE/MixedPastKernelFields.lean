module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

namespace SHE.MixedPastKernelFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastKernelFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastKernelFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastKernelFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastKernelFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastKernelFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastKernelFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastKernelFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastKernelFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastKernelFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The literal random-past mean kernel, in native input/output order. -/
def spatial (k : ℕ) (θ : ℝ) (q : ℝ≥0) (r : ℝ) (t : Fin k→ℝ)
    (z : Ω×NormalizedKernelSplit.Space) : ℂ :=
  weightedSpatial (Base (θ,(U z.1,Dir z.1))) k Λ q r
    (fun _ : Unit=>Mean k θ q z.1) t () z.2.1 z.2.2

def timeField (k : ℕ) (θ : ℝ) (q : ℝ≥0) (r : (Fin k→ℝ)→ℝ)
    (z : ((Fin k→ℝ)×Ω)×NormalizedKernelSplit.Space) : ℂ :=
  spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    k θ q (r z.1.1) z.1.1 (z.1.2,z.2)

attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

theorem timeField_measurable (k : ℕ) (θ : ℝ) (q : ℝ≥0) (r : (Fin k→ℝ)→ℝ) (hr : Measurable r) :
    Measurable (timeField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q r) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hD := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm:=MixedPastLiteralFields.meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q
  let a : ((Fin k→ℝ)×Ω)→ℝ×Inputs:=fun z=>(θ,(U z.2,Dir z.2))
  let m : ((Fin k→ℝ)×Ω)→History HeatCircle k→WordRecursion.State (1+k):=fun z=>Mean k θ q z.2
  have ha : Measurable a:=measurable_const.prodMk ((hU.comp measurable_snd).prodMk (hD.comp measurable_snd))
  have hm' : Measurable (fun z : (((Fin k→ℝ)×Ω)×History HeatCircle k)=>m z.1 z.2):=
    hm.comp (measurable_fst.snd.prodMk measurable_snd)
  have hh:=ControlledFamilyMeanFields.familyWeightedField_measurable P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    a ha k (fun _=>(q:ℝ)) (fun z : (Fin k→ℝ)×Ω=>r z.1) measurable_const (hr.comp measurable_fst)
    m hm' Prod.fst measurable_fst
  convert! hh using 1

def quarterField (k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    ((Fin k→ℝ)×Ω)×NormalizedKernelSplit.Space→ℂ :=
  timeField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q
    (ActualMeanKernel.quarterRowTime (R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k q)

theorem quarterField_measurable (k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    Measurable (quarterField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q) :=
  timeField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q _
    (quarterRowTime_measurable (b:ℝ) k measurable_const measurable_id)

/-- The exact post-old-space moment is jointly Borel in all remaining
old times and native input/output coordinates, before section swapping. -/
def timeMoment (k : ℕ) (θ : ℝ) (q : ℝ≥0) (N : ℕ)
    (z : (Fin k→ℝ)×NormalizedKernelSplit.Space) : ℝ :=
  ∫ ω,‖quarterField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    k θ q ((z.1,ω),z.2)‖^N ∂μ

theorem timeMoment_measurable (k : ℕ) (θ : ℝ) (q : ℝ≥0) (N : ℕ) :
    Measurable (timeMoment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q N) := by
  have hh:=quarterField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q
  have hm:=(hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).norm.pow_const N
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end SHE.MixedPastKernelFields
