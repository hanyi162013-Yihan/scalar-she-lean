module

public import SHE.JointGammaReferenceCurve
public import SHE.FirstGammaCanonicalReference
public import SHE.NativeFrozenPrefixCurve
public import SHE.NativeCanonicalReferenceField
public import SHE.JointGammaCurrentIdentity
public import SHE.NativeJointGammaCurrent
public import SHE.JointInterpolationFields
public import SHE.ScalarCovarianceTailScale
public import SHE.NativeScalarProductAlgebra
public import SHE.JointGammaAffine
public import SHE.FirstGammaEndpointPhysical
public import SHE.FirstGammaEndpointCoherence
public import SHE.FirstGammaCurrentIdentity
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaRows
public import SHE.RescaledRowsCoherence
public import SHE.FiniteSpliceStopCoherence
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.JointGammaReferencePrefix
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaReferencePrefix_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaReferencePrefix_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaReferencePrefix_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaReferencePrefix_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaReferencePrefix_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaReferencePrefix_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaReferencePrefix_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaReferencePrefix_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


local instance jointGammaReferencePrefix_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaReferencePrefix_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaReferencePrefix_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaReferencePrefix_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable (c:ℝ≥0) (hcH:c≤H) (hc1:(c:ℝ)≤1)
local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "OldUM"=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable)
local notation "OldDM"=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v)).measurable)
local notation "Fres" θ=>FrozenReferenceFields.field P Λ κ θ hκP v (NativeCanonicalReferenceField.data OldU OldD)
local notation "FresM" θ=>FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v _
  (NativeCanonicalReferenceField.data_measurable 𝓕 v OldU OldD OldUM OldDM)
local notation "Mres"=>PastFrozenPrefixRows.residual_upper_nonneg P κ hκP
local notation "N0"=>NativeFrozenPrefixCurve.scalar 𝓕 μ H hκ hκ.le
  (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const b c v hcH hc1 I₀
local notation "N1" θ=>NativeFrozenPrefixCurve.scalar 𝓕 μ H (sub_pos.mpr hκP) Mres
  (Fres θ) (FresM θ) b c v hcH hc1 I₁

variable (hH:(H:ℝ)≤1) (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Curve" θ=>JointGammaReferenceCurve.curve 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP v b c hcH hc1 θ

include hH B hBDG hIJ₀ hIJ₁ in
/-- For EVERY root, the actual finite reference agrees at each current
time with a continuous positive-prefix scalar curve on the same drivers. -/
theorem reference_eq_curve (hc0:0<c) (hcb:c<b) (q:ℝ≥0) (hvq:v<q) (hqc:q≤c)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (θ:ℝ) (x:HeatCircle):
    ∀ᵐ ω∂μ,FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ))
      (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ (q,ω)) 0=
      (Curve θ) ((q,ω),x):=by
  have hqb:q<b:=hqc.trans_lt hcb
  have hb0:0<b:=hc0.trans hcb
  have hb1:(b:ℝ)≤1:=(show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
  let Zx:=ScalarCovarianceTailScale.observation (b:ℝ) x
  have hgapx:∀i,(q:ℝ)<(Zx i).target:=fun _=>by exact_mod_cast hqb
  let R:=FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Zx P hκP v q hgapx θ
  have hf:=FirstGammaAbsoluteReference.reference_absolute 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    Zx J P hκP hΛ v q hgapx hH (hb0.trans_le hbH) B hBDG hIJ₀ hIJ₁ θ (hqb.le.trans hbH) hvq.le
  have hp:=FirstGammaEndpointPhysical.value_eq_prefix 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    Zx J P hκP hΛ v b (fun _=>le_rfl) hbH θ q hgapx hH B hBDG hb0 hqb.le q le_rfl
  let A:=NativeFrozenSpatialObservation.row 𝓕 μ H b q v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hqb.le x 0
  let D:=NativeFrozenSpatialObservation.row 𝓕 μ H b q v (sub_pos.mpr hκP) Mres
    (Fres θ) (FresM θ) hbH hqb.le x 0
  have he:StoppedItoInputs.stop 𝓕 μ H q (PastItoInputs.post 𝓕 μ H v (R (Fin.castAdd 1 0)))=
      TwoChannelItoRows.block 𝓕 μ H A D:=by
    simp only [R,FirstGammaRows.replacement,Fin.append_left,PastFrozenPrefixRows.rows]
    rw [PastTwoChannelAlgebra.post_block,TwoChannelItoRows.stop_block]
    simp only [Zx,ScalarCovarianceTailScale.observation]
    rw [←NativeFrozenPrefixBridge.row_eq 𝓕 μ H b q v hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hqb x]
    rw [←NativeFrozenPrefixBridge.row_eq 𝓕 μ H b q v (sub_pos.mpr hκP) Mres
      (FrozenReferenceFields.field P Λ κ θ hκP v (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v))
      (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v _
        (MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)) hbH hqb x]
    rfl
  have hs:∀ᵐω∂μ,J.integral (StoppedItoInputs.stop 𝓕 μ H q (PastItoInputs.post 𝓕 μ H v (R (Fin.castAdd 1 0)))) ω=
      (leftIntegral 𝓕 μ H J).integral A ω+(rightIntegral 𝓕 μ H J).integral D ω:=by
    rw [he,TwoChannelItoRows.integral_block]
    exact Lp.coeFn_add _ _
  have hn0:=NativeFrozenPrefixObservation.noise_observation 𝓕 μ H hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const b c q v hbH hb1 hc0 hcb hqc
    I₀ (leftIntegral 𝓕 μ H J) hIJ₀ B0 hBDG0 x
  have hn1:=NativeFrozenPrefixObservation.noise_observation 𝓕 μ H (sub_pos.mpr hκP) Mres
    (Fres θ) (FresM θ) b c q v hbH hb1 hc0 hcb hqc I₁ (rightIntegral 𝓕 μ H J) hIJ₁ B1 hBDG1 x
  filter_upwards [hf,hp,hs,hn0,hn1] with ω hf hp hs hn0 hn1
  rw [hp]
  have hfi:=hf 0
  change FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ)) _ 0=_ at hfi
  rw [hfi,hs]
  change _=functional ((b:ℝ)-(v:ℝ)) x
    (S.first v ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • (S.second v ω-S.first v ω))+
    functional ((b:ℝ)-(c:ℝ)) x _+functional ((b:ℝ)-(c:ℝ)) x _
  rw [hn0,hn1,map_add,map_smul]
  dsimp only [Zx,ScalarCovarianceTailScale.observation]
  ring

end SHE.JointGammaReferencePrefix
