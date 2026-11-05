module

public import SHE.MixedFirstDefectInputBounds
public import SHE.DefectOriginalConvolution
public import SHE.DefectGapConvolution
public import SHE.MixedFirstDefectRelativeEnergy
public import SHE.MixedFirstDefectRMS
public import SHE.MixedCanonicalRootFields
public import SHE.DefectRelativeFactor
public import SHE.DefectCombinedTime
public import SHE.NativeBesselFieldAE
public import SHE.NativeSignedHaarProcess
public import SHE.ControlledScalarReference
public import SHE.ControlledThetaDefectEnvelope
public import SHE.MixedJointUncutDefectTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.MixedFirstDefectConvolutionTransport
open Set MeasureTheory Real AddCircle StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
  NativeHeatObservation CutoffWordLevel CutoffWordHistories CutoffCarriers ControlledProfile
  ControlledReferenceLevel PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw
open scoped NNReal ENNReal BigOperators
open Classical
local instance mixedFirstDefectRMS_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedFirstDefectRMS_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedFirstDefectRMS_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedFirstDefectRMS_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))
variable (θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformSmooth.UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Z"=>ControlledScalarReference.observations b
local notation "Base"=>ControlledReferenceThetaGeometry.level P (fun z=>κ+aV z) hAs Λ v b hvb Z
  (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ 0 v b hvb (0,0)


local notation "Conv"=>MixedFirstDefectRMS.convolution
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs v b hvb F hF hFm
local notation "RMS"=>MixedActualNegativeRMS.rms
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "InputE"=>MixedFirstDefectRMS.inputEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S

/-- The literal original first-defect convolution is dominated by the
proved complete positive gap mixture on the SAME original input. The
coarse boundedness check only proves L1; it does not enter the bound. -/
theorem le_relative (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρ1:ρ≤1)(k:ℕ)
    (h:ℝ)(hh:0<h)(hspan:(b:ℝ)-(v:ℝ)≤h)(hpos:v<b)(hbH:b≤H)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)(ω:Ω):
    Conv ρ hL hρ.le k A0 ν ω≤
      MixedFirstDefectRelativeEnergy.value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
        (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h A0 ν k ρ hL hρ.le (b,ω):=by
  let f:ℝ→ℝ:=fun q=>ScalarTimeZeroExtension.extend H (RMS ρ hL hρ.le) (q,ω)
  have hf:Measurable f:=(ScalarTimeZeroExtension.measurable H (RMS ρ hL hρ.le)
    (MixedActualNegativeRMS.measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ.le)).comp
        (measurable_id.prodMk measurable_const)
  have hbound(q:ℝ):0≤f q ∧ f q≤|M-ell|:=
    MixedFirstDefectInputBounds.extended_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ.le (q,ω)
  have he:Conv ρ hL hρ.le k A0 ν ω=
      DefectOriginalConvolution.convolution Zero P
        (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) Λ ρ A0 ν k f:=by
    unfold MixedFirstDefectRMS.convolution DefectOriginalConvolution.convolution
    apply integral_congr_ae
    filter_upwards with t
    dsimp only
    split_ifs
    · change MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k t A0 ν*
        (∫q:ℝ,MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k t q*
          sqrt (InputE ρ hL hρ.le q ω) ∂volume.restrict
            (Ioc (v:ℝ) ((carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0)))))=_
      unfold MixedFirstDefectRMS.oldFactor DefectOriginalConvolution.oldFactor
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
      have hqH:q∈Ioc (0:ℝ) (H:ℝ):=⟨lt_of_le_of_lt v.2 hq.1,
        (hq.2.trans ((carrier Zero k).terminal_horizon _)).trans (by exact_mod_cast hbH)⟩
      rw [MixedFirstDefectInputRMS.input_eq_extended
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ.le q ω hqH]
      rfl
    · rfl
  rw [he]
  have hδ:0<ControlledOldIntervals.fraction P*P.lower:=
    mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos
  have hgap:=DefectOriginalConvolution.eq_gap Zero P
    (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
    b (fun _=>rfl) (by exact_mod_cast hpos) (fun _ _=>rfl) Λ ρ A0 ν hA0 hν k f
  rw [hgap]
  have hmix:=DefectGapConvolution.le_mixture P hδ (zero_lt_one.trans_le hL) hρ hρ1 hh hspan
    (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k hA0 hν f hf
      (fun q=>(hbound q).1) |M-ell| (fun q=>(hbound q).2) b
  apply hmix.trans_eq
  apply integral_congr_ae
  filter_upwards with p
  change f ((b:ℝ)-(∑i,p.1 i)-p.2)=f ((b:ℝ)-MixedFirstDefectRelativeEnergy.shift k p)
  congr 1
  unfold MixedFirstDefectRelativeEnergy.shift
  ring

end SHE.MixedFirstDefectConvolutionTransport
