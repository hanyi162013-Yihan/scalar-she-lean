module
public import SHE.MixedPastSignedEndpointMoments
public import SHE.MixedPastSignedEndpointTrace
public import SHE.RawTraceRMS
public import SHE.MixedPastKernelSections
public import SHE.RelativeKernelTruncationZero
public import SHE.ControlledFamilyKernelBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false

namespace SHE.MixedPastSignedEndpointRMS
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastSignedEndpointMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastSignedEndpointMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastSignedEndpointMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastSignedEndpointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastSignedEndpointMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastSignedEndpointMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastSignedEndpointMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastSignedEndpointMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastSignedEndpointMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

open ActualMeanKernel NativeRandomKernel NormalizedKernelSplit NativeSignedHaarProcess SignedKernelTruncation
local notation "Endpoint"=>MixedPastKernelFields.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

include hIJ₀ hIJ₁ in
/-- The genuine endpoint signed columns have a sharp section RMS bound
on the original sample measure. The current negative-input energy is
retained, and the bad part has arbitrary polynomial truncation decay. -/
theorem energy (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x,(Z.observations x 0).center=x)(hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
    (k:ℕ)(hfresh:(b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ)(B0:ℝ≥0)(hBDG:StandardTerminalBDGPower ((order+1)*(k+2)) J B0)
    (q:ℝ≥0)(hvq:v≤q)(hqH:q≤H)(hwidth1:(b:ℝ)-(q:ℝ)≤1)
    (mass ρ lam ε tail η:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(htail:tail≤ε*(2*order))(hη:0<η):
    let R0:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let C:=MixedPastWordMoments.momentConstant P k k (order+1)
      ((k:ℝ)*(NativeHybridMoments.momentConstant ((order+1)*(k+2)) B0 κ M)^P.exponent)
    let E:=∫ω,inputEnergy hmass hρ.le (CU (q,ω)) (CV (q,ω)) ∂μ
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      QuarterSpatialEvent.active Zero (b:ℝ) k q t→
      let δ:=quarterTraceTime (R:=R0) (b:ℝ) k q t
      let w:=PastMeanEnvelope.width (R:=R0) (b:ℝ) k q t
      let D:=PastMeanAmplitude.damped Zero P k Λ q A0 ν (QuarterSpatialEvent.anchor k t)*
        ScalarMeanEnvelope.massCoefficient k 1*sqrt δ
      let raw:=SignedKernelColumns.rawColumns (Endpoint k 1 q q t) mass ρ hmass hρ.le ell M hell
        (fun ω=>CU (q,ω)) (fun ω=>CV (q,ω))
      Integrable (fun ω=>‖raw ω‖^2) μ ∧ (∫ω,‖raw ω‖^2 ∂μ)≤
        (RawTraceTimeEnvelope.goodAmplitude Jt ρ η (lam^ε) D δ w*sqrt E+
          RawTraceTimeEnvelope.badAmplitude M C D δ lam tail)^2:=by
  intro R0 Jt C E
  have hm:=MixedPastSignedEndpointMoments.separated_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet
    order B0 hBDG q hvq hqH hwidth1 mass ρ lam ε tail hmass hρ hρhalf hlam htail
  have hJ:0≤Jt:=(MixedPastSignedEndpointMoments.traceConstant_pos (Ω:=Ω) (M:=M) hell ρ hρ hρhalf).le
  have hM:0≤M:=(hell.trans_le (hbU 0).1).le.trans (hbU 0).2
  have hC:0≤C:=MixedPastWordMoments.momentConstant_nonneg P k k (order+1) _
  have hE:0≤E:=integral_nonneg (fun _=>sq_nonneg _)
  filter_upwards [hm] with t ht
  intro ha δ w D raw
  let r:=quarterRowTime (R:=R0) (b:ℝ) k q t
  obtain ⟨_,hqr,hr,hδ,_,heδ⟩:=quarter_geometry (R:=R0) (b:ℝ) k (q:ℝ) t ha.2
  have hterminal:fixedTerminal (R:=R0) (b:ℝ) k t≤(b:ℝ):=by
    rw [←terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)]
    exact (terminal_le_initial Zero k _).trans_eq (by rfl)
  obtain ⟨hw,_,_,hδw⟩:=quarter_widths (R:=R0) ha.2 hterminal
  have hD:0≤D:=mul_nonneg (mul_nonneg
    (PastMeanAmplitude.damped_nonneg Zero P k Λ q A0 ν _) (ScalarMeanEnvelope.massCoefficient_nonneg k zero_le_one))
    (sqrt_nonneg _)
  have hh:=ht ha
  have heq(ω:Ω):‖raw ω‖^2=SignedKernelEnergy.energy (Endpoint k 1 q r t) mass ρ δ hmass hρ.le
      (quarterTraceTime_nonneg (b:ℝ) k q t) (CU (q,ω)).1 (CV (q,ω)).1 ω:=by
    have h:=MixedPastSignedEndpointTrace.raw_trace_eq
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      hΛ k 1 q r t hqr.le hr hmass hρ.le (fun ω=>CU (q,ω)) (fun ω=>CV (q,ω)) ω
    have hδeq:2*(r-(q:ℝ))=δ:=heδ
    simpa only [hδeq] using h
  have heqf:=funext heq
  refine ⟨hh.1.congr (ae_of_all _ (fun ω=>(heq ω).symm)),?_⟩
  rw [heqf]
  exact RawTraceTimeEnvelope.energy_envelope hJ hη hδ hδw hM hC
    (Real.rpow_nonneg (zero_lt_one.trans_le hlam).le _) hD (zero_lt_one.trans_le hlam) hE ρ tail hh.2

end SHE.MixedPastSignedEndpointRMS
