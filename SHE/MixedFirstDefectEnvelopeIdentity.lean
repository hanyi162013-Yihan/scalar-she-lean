module
public import SHE.MixedFirstDefectPointSections

public import SHE.MixedFirstDefectNormEnvelope
public import SHE.MixedFirstDefectConvolutionTransport
public import SHE.MixedFirstDefectMinkowski
public import SHE.MixedFirstDefectDisintegration
public import SHE.NativeBesselParameterSection
public import SHE.MixedFirstDefectIntegral
public import SHE.MixedJointActiveVolume
public import SHE.MixedFirstDefectRMS
public import SHE.ControlledReferenceFamilyDefectL1
public import SHE.RootHistoryCurrentMeasure
public import SHE.NativeBesselParameterAverageAE
public import SHE.HistoryMeasureGeometry
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

namespace SHE.MixedFirstDefectEnvelopeIdentity
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



local notation "Sp"=>MixedFirstDefectRMS.spatialPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs θ v b hvb F hF hFm
local notation "PV"=>MixedFirstDefectRMS.pointValue
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs θ v b hvb F hF hFm
local notation "Val"=>MixedFirstDefectRMS.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs θ v b hvb F hF hFm
local notation "Env"=>MixedFirstDefectNormEnvelope.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs v b hvb F hF hFm
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

theorem envelope_eq (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(k:ℕ)(hbH:b≤H)
    (A0 ν:ℝ)(ω:Ω)(a:(Fin k→ℝ)×ℝ):
    MixedFirstDefectPointSections.envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P hAs v b hvb F hF hFm ρ hL hρ k A0 ν ω a=Env ρ hL hρ k A0 ν ω a:=by
  let z:=separated k ((0:HeatCircle),a.1,fun _=>0)
  let old:=MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k a.1 A0 ν
  let K:=MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k a.1 a.2
  let I:=MixedFirstDefectRMS.inputEnergy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S ρ hL hρ a.2 ω
  let f:=ScalarTimeZeroExtension.extend H (MixedActualNegativeRMS.rms
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ)
  by_cases hp:StrictHistory Zero k z
  · have hterm:(carrier Zero k).terminal z=DefectOriginalEnvelope.edge b k a.1:=by
      rw [PhysicalOrderedGaps.terminal_eq_boundary Zero b (fun _=>rfl) k a.1 0 (fun _=>0) hp]
      dsimp only [DefectOriginalEnvelope.edge]
      rw [OrderedGapCoordinates.sum_gaps]
      ring
    have hpair:K=DefectGapKernelMass.realKernel Λ ρ k (OrderedGapCoordinates.gaps b k a.1)
        ((carrier Zero k).terminal z-a.2):=
      DefectOriginalConvolution.pair_eq Zero b (fun _=>rfl) (fun _ _=>rfl) Λ ρ k a.1 a.2 hp
    change (if StrictHistory Zero k z ∧ (v:ℝ)<a.2 ∧ a.2≤(carrier Zero k).terminal z then
      old*K*sqrt I else 0)=
      (if StrictHistory Zero k z then old else 0)*
        (if (v:ℝ)<a.2 ∧ a.2≤DefectOriginalEnvelope.edge b k a.1 then
          DefectGapKernelMass.realKernel Λ ρ k (OrderedGapCoordinates.gaps b k a.1)
            (DefectOriginalEnvelope.edge b k a.1-a.2)*f (a.2,ω) else 0)
    rw [if_pos hp,←hterm]
    by_cases hq:(v:ℝ)<a.2 ∧ a.2≤(carrier Zero k).terminal z
    · rw [if_pos ⟨hp,hq⟩,if_pos hq,←hpair]
      have hqH:a.2∈Ioc (0:ℝ) (H:ℝ):=⟨(NNReal.coe_nonneg v).trans_lt hq.1,
        hq.2.trans ((terminal_le_initial Zero k z).trans (by exact_mod_cast hbH))⟩
      have hi:=MixedFirstDefectInputRMS.input_eq_extended
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ a.2 ω hqH
      change sqrt I=f (a.2,ω) at hi
      rw [hi]
      ring
    · rw [if_neg (fun h=>hq h.2),if_neg hq,mul_zero]
  · change (if StrictHistory Zero k z ∧ (v:ℝ)<a.2 ∧ a.2≤(carrier Zero k).terminal z then
      old*K*sqrt I else 0)=
      (if StrictHistory Zero k z then old else 0)*_
    rw [if_neg (fun h=>hp h.1),if_neg hp,zero_mul]

end SHE.MixedFirstDefectEnvelopeIdentity
