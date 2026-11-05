module
public import SHE.MixedPastNativeHaarFields
public import SHE.MixedPastKernelSections
public import SHE.RelativeKernelTruncationZero
public import SHE.ControlledFamilyKernelBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false

namespace SHE.MixedPastSignedEndpointMoments
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

/-- This signed trace constant is selected before the profile,
smoothing index, damping parameter and actual coupled model. -/
def traceConstant (ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2):ℝ:=
  Classical.choose (exists_expected_relative_nonnegative (Ω:=Ω) ell M hell hρ hρhalf)

theorem traceConstant_pos (ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2):
    0<traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf:=
  (Classical.choose_spec (exists_expected_relative_nonnegative (Ω:=Ω) ell M hell hρ hρhalf)).1

include hIJ₀ hIJ₁ in
/-- Actual theta-one stop-weighted endpoint against the original
same-Haar coefficient difference, after the genuine quarter split.
Conditional varying-profile Gaussian moments and all spatial/trace
applicability are discharged; the true negative-input energy remains. -/
theorem separated_energy (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
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
    (mass ρ lam ε tail:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(htail:tail≤ε*(2*order)):
    let R0:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    let Jt:=traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let C:=MixedPastWordMoments.momentConstant P k k (order+1)
      ((k:ℝ)*(NativeHybridMoments.momentConstant ((order+1)*(k+2)) B0 κ M)^P.exponent)
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      QuarterSpatialEvent.active Zero (b:ℝ) k q t→
      let r:=quarterRowTime (R:=R0) (b:ℝ) k q t
      let δ:=quarterTraceTime (R:=R0) (b:ℝ) k q t
      let w:=PastMeanEnvelope.width (R:=R0) (b:ℝ) k q t
      let D:=PastMeanAmplitude.damped Zero P k Λ q A0 ν (QuarterSpatialEvent.anchor k t)*
        ScalarMeanEnvelope.massCoefficient k 1*sqrt δ
      let energy:=fun ω=>SignedKernelEnergy.energy (Endpoint k 1 q r t) mass ρ δ hmass hρ.le
        (quarterTraceTime_nonneg (b:ℝ) k q t) (CU (q,ω)).1 (CV (q,ω)).1 ω
      Integrable energy μ ∧ (∫ω,energy ω ∂μ)≤
        2*goodCost Jt ρ δ w (lam^ε) (heatAmplitude D δ w)*
          (∫ω,inputEnergy hmass hρ.le (CU (q,ω)) (CV (q,ω)) ∂μ)+
        8*M*C*heatMassConstant*D^2*δ^(-1:ℝ)*lam^(-tail):=by
  intro R0 Jt C
  have htrace:=(Classical.choose_spec (exists_expected_relative_nonnegative (Ω:=Ω) ell M hell hρ hρhalf)).2
  have hc:Measurable (fun ω=>CU (q,ω)):=
    (S.first_coefficient.mono (predictable_le_product 𝓕)).measurable.comp
      (measurable_const.prodMk measurable_id)
  have hd:Measurable (fun ω=>CV (q,ω)):=
    (S.second_coefficient.mono (predictable_le_product 𝓕)).measurable.comp
      (measurable_const.prodMk measurable_id)
  have hC:0≤C:=MixedPastWordMoments.momentConstant_nonneg P k k (order+1) _
  have hmoment:=MixedPastKernelSections.normalized_quarter_moment
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hages hrootStop hrootTarget hcenter hspan k hfresh hold 1 (by norm_num) A0 ν hA0 hν hjet
    (order+1) (by omega) B0 hBDG q hvq hqH
  filter_upwards [hmoment] with t ht
  intro ha r δ w D energy
  obtain ⟨_,hqr,hr,hδ,_,heδ⟩:=quarter_geometry (R:=R0) (b:ℝ) k (q:ℝ) t ha.2
  have hterminal:fixedTerminal (R:=R0) (b:ℝ) k t≤(b:ℝ):=by
    rw [←terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)]
    exact (terminal_le_initial Zero k _).trans_eq (by rfl)
  obtain ⟨hw,hww,_,hδw⟩:=quarter_widths (R:=R0) ha.2 hterminal
  have hD:0≤D:=mul_nonneg (mul_nonneg
    (PastMeanAmplitude.damped_nonneg Zero P k Λ q A0 ν _) (ScalarMeanEnvelope.massCoefficient_nonneg k zero_le_one))
    (sqrt_nonneg _)
  have hField:Measurable (Endpoint k 1 q r t):=by
    have hh:=MixedPastKernelFields.quarterField_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k 1 q
    have hp:Measurable (fun z:Ω×Space=>((t,z.1),z.2)):=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    have hc:=hh.comp hp
    change Measurable (Endpoint k 1 q (quarterRowTime (R:=R0) (b:ℝ) k q t) t) at hc
    exact hc
  obtain ⟨B,hB,hb⟩:=ControlledFamilyKernelBounds.weightedSpatial_family_uniform_bound
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k hΛ q r t
  have hbound(ω:Ω)(y x:HeatCircle):‖Endpoint k 1 q r t (ω,(y,x))‖≤B:=
    hb (1,(U ω,Dir ω)) (MixedPastLiteralPoint.meanField
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k 1 q ω) y x
  have hi(z:Space):Integrable (fun ω=>‖Endpoint k 1 q r t (ω,z)‖^(2*order+2)) μ:=
    (integrable_const (B^(2*order+2))).mono'
      (((hField.comp (measurable_id.prodMk measurable_const)).norm.pow_const _).aestronglyMeasurable)
      (ae_of_all _ (fun ω=>by rw [Real.norm_of_nonneg (by positivity)];exact pow_le_pow_left₀ (norm_nonneg _) (hbound ω z.1 z.2) _))
  have hAmp:heatAmplitude D δ w=PastMeanEnvelope.amplitude Zero P (b:ℝ) k Λ q A0 ν t:=by
    have hcancel:sqrt δ*δ^(-(1/2:ℝ))=1:=by
      rw [sqrt_eq_rpow,←Real.rpow_add hδ]
      norm_num
    unfold heatAmplitude PastMeanEnvelope.amplitude
    dsimp only [D,w]
    calc
      _=(PastMeanAmplitude.damped Zero P k Λ q A0 ν (QuarterSpatialEvent.anchor k t)*
          ScalarMeanEnvelope.massCoefficient k 1*w^(1/4:ℝ))*(sqrt δ*δ^(-(1/2:ℝ))):=by ring
      _=_:=by rw [hcancel];ring
  have hMom:∀ᵐz:Space∂(haarAddCircle (T:=2*Real.pi)).prod haarAddCircle,
      (∫ω,‖Endpoint k 1 q r t (ω,z)‖^(2*order+2) ∂μ)≤C*(heatEnvelope D δ w z)^(2*order+2):=by
    filter_upwards [ht ha] with z hz
    have hpow:2*(order+1)=2*order+2:=by omega
    simpa only [MixedPastKernelFields.timeMoment,MixedPastKernelFields.quarterField,
      MixedPastKernelFields.timeField,hpow,PastMeanEnvelope.envelope,heatEnvelope,hAmp,r,w] using hz
  exact htrace μ mass δ w D lam ε tail C hmass hδ hw (hww.trans hwidth1) hδw hD hlam hC order htail
    (Endpoint k 1 q r t) hField (fun _=>Complex.ofReal_im _) B hB hbound (ae_of_all _ hi) hMom
    (fun ω=>CU (q,ω)) (fun ω=>CV (q,ω)) hc hd

end SHE.MixedPastSignedEndpointMoments

