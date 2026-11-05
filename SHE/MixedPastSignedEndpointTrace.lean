module
public import SHE.MixedPastNativeHaarFields
public import SHE.MixedPastKernelSections
public import SHE.VariableMeanOperator
public import SHE.RelativeKernelTruncationZero
public import SHE.RawKernelColumns
public import SHE.NativeKernelCongruence
public import SHE.ControlledFamilyKernelBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false

namespace SHE.MixedPastSignedEndpointTrace
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastSignedEndpointTrace_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastSignedEndpointTrace_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastSignedEndpointTrace_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastSignedEndpointTrace_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastSignedEndpointTrace_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastSignedEndpointTrace_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastSignedEndpointTrace_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastSignedEndpointTrace_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastSignedEndpointTrace_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Frame"=>MixedPastNativeKernelTrace.frame Λ P haP v b hvb Z htarget hstop F hF hFm

local notation "Current"=>MixedPastNativeKernelEnergy.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RowVariance"=>MixedPastNativeKernelEnergy.rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm
local notation "RowResidual"=>MixedPastNativeKernelEnergy.rowResidual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "AAmp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm


local notation "Spatial"=>MixedPastNativeKernelAverage.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "PastEnergy"=>MixedPastNativeKernelActual.pastEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CurrentEnergy"=>MixedPastNativeKernelActual.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelAverage.spatial
  MixedPastNativeKernelActual.pastEnergy MixedPastNativeKernelActual.currentEnergy MixedPastWordMoments.total
  MixedPastLiteralPoint.meanField MixedPastKernelFields.spatial MixedPastJointData.pastU MixedPastJointData.pastD

local notation "Mean"=>MixedPastLiteralPoint.meanField
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Endpoint"=>MixedPastKernelFields.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
open ActualMeanKernel NativeRandomKernel NormalizedKernelSplit NativeSignedHaarProcess SignedKernelTruncation

/-- Exact right-heat factorization for the original varying-past
endpoint kernel. Reference, current law, baselines and stop weights
remain fixed samplewise while only the physical direction row moves. -/
theorem operator_split (hΛ:0≤Λ)(k:ℕ)(θ:ℝ)(q:ℝ≥0)(r:ℝ)(t:Fin k→ℝ)
    (hqr:(q:ℝ)≤r)
    (hr:r<ActualMeanKernel.fixedTerminal
      (R:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k t)(ω:Ω):
    integralOperator (Endpoint k θ q q t) ω=
      (integralOperator (Endpoint k θ q r t) ω).comp
        (circleHeatOperator (r-(q:ℝ)) (sub_nonneg.mpr hqr)):=by
  let Ref:=fun a:ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2
  let a:Ω→ℝ×Inputs:=fun z=>(θ,(U z,Dir z))
  have hm:∀z,Measurable (Mean k θ q z):=by
    intro z
    have hh:=MixedPastLiteralFields.meanField_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q
    have hp:Measurable (fun h:History HeatCircle k=>(z,h)):=measurable_const.prodMk measurable_id
    have hc:=hh.comp hp
    exact hc
  have hfix {R R':ReferenceData}(he:R.base=R'.base)(T:ℝ)(j:ℕ)(times:Fin j→ℝ):
      fixedTerminal (R:=R) T j times=fixedTerminal (R:=R') T j times:=by
    induction j with
    | zero=>rfl
    | succ j ih=>simp only [fixedTerminal];rw [he,ih]
  have hr'(z:Ω):r<fixedTerminal (R:=Ref (a z)) (b:ℝ) k t:=by
    have hf:=hfix (R:=Ref (a z)) (R':=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) rfl (b:ℝ) k t
    exact hr.trans_eq hf.symm
  have hh:=family_weighted_operator_split Ref Base a k (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>r)
    (fun _=>(b:ℝ)) (fun _ _=>rfl) (fun _=>hΛ) (Mean k θ q) hm (fun _=>t)
    (fun _=>hqr) hr' ω
  unfold ActualMeanKernel.familyWeightedField at hh
  unfold MixedPastKernelFields.spatial
  dsimp only [Ref,a] at hh
  exact hh

/-- The endpoint signed Haar trace is the literal separated trace;
the coefficient difference stays on the original common Haar driver. -/
theorem raw_trace_eq (hΛ:0≤Λ)(k:ℕ)(θ:ℝ)(q:ℝ≥0)(r:ℝ)(t:Fin k→ℝ)
    (hqr:(q:ℝ)≤r)
    (hr:r<ActualMeanKernel.fixedTerminal
      (R:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k t)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    (c d:Ω→EllipticField ell M)(ω:Ω):
    ‖SignedKernelColumns.rawColumns (Endpoint k θ q q t) mass ρ hmass hρ ell M hell c d ω‖^2=
      SignedKernelEnergy.energy (Endpoint k θ q r t) mass ρ (2*(r-(q:ℝ))) hmass hρ
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hqr)) (c ω).1 (d ω).1 ω:=by
  rw [SignedKernelColumns.rawColumns_norm_sq]
  unfold SignedKernelEnergy.energy
  simp only [show 2*(r-(q:ℝ))/2=r-(q:ℝ) by ring]
  apply tsum_congr
  intro j
  rw [operator_split 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ k θ q r t hqr hr ω,ContinuousLinearMap.comp_apply]

end SHE.MixedPastSignedEndpointTrace

