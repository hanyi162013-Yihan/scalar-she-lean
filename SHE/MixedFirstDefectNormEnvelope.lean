module

public import SHE.MixedFirstDefectInputBounds
public import SHE.DefectOriginalEnvelopeIntegral
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

namespace SHE.MixedFirstDefectNormEnvelope
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


def value (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(k:ℕ)(A0 ν:ℝ)(ω:Ω):((Fin k→ℝ)×ℝ)→ℝ:=
  DefectOriginalEnvelope.value Zero P
    (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) b Λ ρ A0 ν k
      (fun q=>ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) (q,ω))

local notation "E"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P hAs v b hvb F hF hFm

/-- The actual first-defect source norm envelope is measurable,
nonnegative and integrable in its original old/current time variables.
The coarse coefficient bound is used only to justify this L1 statement. -/
theorem integrable (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρ1:ρ≤1)(k:ℕ)
    (hpos:v<b)(A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)(ω:Ω):
    Measurable (E ρ hL hρ.le k A0 ν ω) ∧
      (∀p,0≤E ρ hL hρ.le k A0 ν ω p) ∧
      Integrable (E ρ hL hρ.le k A0 ν ω)
        ((Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume):=by
  let f:ℝ→ℝ:=fun q=>ScalarTimeZeroExtension.extend H (RMS ρ hL hρ.le) (q,ω)
  have hf:Measurable f:=(ScalarTimeZeroExtension.measurable H (RMS ρ hL hρ.le)
    (MixedActualNegativeRMS.measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ.le)).comp
        (measurable_id.prodMk measurable_const)
  have hb(q:ℝ):0≤f q ∧ f q≤|M-ell|:=
    MixedFirstDefectInputBounds.extended_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ.le (q,ω)
  have hδ:0<ControlledOldIntervals.fraction P*P.lower:=
    mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos
  exact DefectOriginalEnvelope.integrable Zero P hδ (zero_lt_one.trans_le hL) hρ hρ1
    (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) b (fun _=>rfl)
    (by exact_mod_cast hpos) (h:=(b:ℝ)-(v:ℝ)) le_rfl k A0 ν hA0 hν
    f hf (fun q=>(hb q).1) |M-ell| (fun q=>(hb q).2)

/-- The actual envelope integral is exactly the retained original
convolution. In particular the q-input remains inside the time integral. -/
theorem integral_eq (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(k:ℕ)
    (hpos:v<b)(hbH:b≤H)(A0 ν:ℝ)(ω:Ω)
    (hi:Integrable (E ρ hL hρ k A0 ν ω)
      ((Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume)):
    (∫p:(Fin k→ℝ)×ℝ,E ρ hL hρ k A0 ν ω p
      ∂(Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume)=
        Conv ρ hL hρ k A0 ν ω:=by
  let f:ℝ→ℝ:=fun q=>ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) (q,ω)
  have he:Conv ρ hL hρ k A0 ν ω=
      DefectOriginalConvolution.convolution Zero P
        (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) Λ ρ A0 ν k f:=by
    unfold MixedFirstDefectRMS.convolution DefectOriginalConvolution.convolution
    apply integral_congr_ae
    filter_upwards with t
    dsimp only
    split_ifs
    · change MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k t A0 ν*
        (∫q:ℝ,MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k t q*
          sqrt (InputE ρ hL hρ q ω) ∂volume.restrict
            (Ioc (v:ℝ) ((carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0)))))=_
      unfold MixedFirstDefectRMS.oldFactor DefectOriginalConvolution.oldFactor
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
      have hqH:q∈Ioc (0:ℝ) (H:ℝ):=⟨lt_of_le_of_lt v.2 hq.1,
        (hq.2.trans ((carrier Zero k).terminal_horizon _)).trans (by exact_mod_cast hbH)⟩
      rw [MixedFirstDefectInputRMS.input_eq_extended
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ q ω hqH]
      rfl
    · rfl

  rw [he]
  exact DefectOriginalEnvelopeIntegral.integral_eq Zero P
    (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) b
    (fun _=>rfl) (by exact_mod_cast hpos) (fun _ _=>rfl) Λ ρ A0 ν k f hi

end SHE.MixedFirstDefectNormEnvelope
