module

public import SHE.FirstGammaEndpointReferenceAbsolute
public import SHE.FullHorizonEndpointStop
public import SHE.FirstGammaAbsoluteReference
public import SHE.NativeFrozenPrefixBridge
public import SHE.ScalarCovarianceTailScale
public import SHE.FirstGammaEndpointPhysical
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaValues
public import SHE.FiniteReferenceSpliceRows
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaEndpointReferenceNative
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaCanonicalReference_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaCanonicalReference_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaCanonicalReference_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaCanonicalReference_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaCanonicalReference_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaCanonicalReference_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaCanonicalReference_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaCanonicalReference_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance firstGammaCanonicalReference_period : Fact (0<2*Real.pi):=⟨by positivity⟩
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
variable (hΛ : 0≤Λ) (v c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)


open FirstGammaConstruction
local notation "Rold" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap
local notation "Rnew" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap
local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
variable (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "OldUM"=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable)
local notation "OldDM"=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v)).measurable)

include hH B hBDG hIJ₀ hIJ₁ in
/-- The actual finite compatible reference at the SINGULAR terminal
endpoint is the actual common-noise canonical Hilbert reference field.
All positive-prefix limits have been proved in the original input space. -/
theorem endpoint_eq_field (b:ℝ≥0)(hbH:b≤H)(hvb:v<b)
    (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)(θ:ℝ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
      FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ))
        (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ (b,ω)) 0=
      PredictableScalarField.nativeField
        (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM
          hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ θ (b,ω)) (ω,x):=by
  have hb1:(b:ℝ)≤1:=(show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
  have hn:=NativeCanonicalReferenceObservation.observation 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM
    hbH hb1 I₀ I₁ J hIJ₀ hIJ₁ b hvb le_rfl B0 B1 hBDG0 hBDG1 θ
  filter_upwards [hn] with x hn
  let Zx:=ScalarCovarianceTailScale.observation (b:ℝ) x
  let R:=FirstGammaEndpointRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    Zx P hκP v b (fun _=>le_rfl) hbH θ
  have hf:=FirstGammaEndpointReferenceAbsolute.terminal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Zx J P hκP hΛ v b (fun _=>le_rfl) hbH B hBDG θ hH hIJ₀ hIJ₁ hvb
  let A:=NativeFrozenSpatialObservation.row 𝓕 μ H b b v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH le_rfl x 0
  let D:=NativeFrozenSpatialObservation.row 𝓕 μ H b b v (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
    (FrozenReferenceFields.field P Λ κ θ hκP v (NativeCanonicalReferenceField.data OldU OldD))
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v _
      (NativeCanonicalReferenceField.data_measurable 𝓕 v OldU OldD OldUM OldDM)) hbH le_rfl x 0
  have he:StoppedItoInputs.stop 𝓕 μ H b (PastItoInputs.post 𝓕 μ H v (R (Fin.castAdd 1 0)))=
      TwoChannelItoRows.block 𝓕 μ H A D:=by
    simp only [R,FirstGammaEndpointRows.replacement,Fin.append_left]
    rw [TwoChannelPastDifference.stop_post,TwoChannelItoRows.stop_block]
    simp only [FirstGammaEndpointRows.additive,FirstGammaEndpointRows.frozen]
    dsimp only [Zx,ScalarCovarianceTailScale.observation]
    rw [FullHorizonEndpointStop.self,FullHorizonEndpointStop.self,PastTwoChannelAlgebra.post_block]
    simp only [A,D,NativeFrozenSpatialObservation.row,max_self,add_zero]
    rfl
  have hs:∀ᵐω∂μ,J.integral (StoppedItoInputs.stop 𝓕 μ H b
      (PastItoInputs.post 𝓕 μ H v (R (Fin.castAdd 1 0)))) ω=
      (leftIntegral 𝓕 μ H J).integral A ω+(rightIntegral 𝓕 μ H J).integral D ω:=by
    rw [he,TwoChannelItoRows.integral_block]
    exact Lp.coeFn_add _ _
  filter_upwards [hn,hf,hs] with ω hn hf hs
  have hfi:=hf 0
  change FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ)) _ 0=_ at hfi
  rw [hfi]
  rw [hn,map_add,map_smul]
  change _=functional ((b:ℝ)-(v:ℝ)) x (S.first v ω)+
    (θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))*functional ((b:ℝ)-(v:ℝ)) x (S.second v ω-S.first v ω)+
    (leftIntegral 𝓕 μ H J).integral A ω+(rightIntegral 𝓕 μ H J).integral D ω
  rw [hs]
  dsimp only [FirstGammaEndpointReferenceAbsolute.initial,Zx,ScalarCovarianceTailScale.observation]
  ring

end SHE.FirstGammaEndpointReferenceNative
