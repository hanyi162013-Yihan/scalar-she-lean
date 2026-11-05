module

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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaCanonicalReference
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
/-- The actual SINGULAR finite endpoint reference is the genuine jointly
predictable canonical native field on every positive-age current
prefix, on one native-root/sample event. No spatial-version premise is
assumed for the original finite-Ito construction. -/
theorem reference_eq_field (T : ℝ≥0) (hcT : c<T) (hTH : T≤H) (hvc : v<c)
    (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I₀ B0) (hBDG1 : StandardTerminalBDG16 I₁ B1) (θ : ℝ) :
    ∀ᵐ x : HeatCircle∂AddCircle.haarAddCircle,∀ᵐ ω∂μ,
      FirstGammaAffine.reference 1 Λ θ (fun _=>(T:ℝ))
        (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (ScalarCovarianceTailScale.observation T x) J P hκP hΛ v T (fun _=>le_rfl) hTH θ (c,ω)) 0=
      PredictableScalarField.nativeField
        (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H T v P Λ κ hκ hκP OldU OldD OldUM OldDM
          hTH ((show (T:ℝ)≤(H:ℝ) by exact_mod_cast hTH).trans hH) I₀ I₁ θ (c,ω)) (ω,x) := by
  have hcH:c≤H:=hcT.le.trans hTH
  have hT0:0<T:=(show (0:ℝ≥0)≤v from by exact_mod_cast v.coe_nonneg).trans_lt (hvc.trans hcT)
  have hT1:(T:ℝ)≤1:=(show (T:ℝ)≤(H:ℝ) by exact_mod_cast hTH).trans hH
  have hn:=NativeCanonicalReferenceObservation.observation 𝓕 μ H T v P Λ κ hκ hκP OldU OldD OldUM OldDM
    hTH hT1 I₀ I₁ J hIJ₀ hIJ₁ c hvc hcT.le B0 B1 hBDG0 hBDG1 θ
  filter_upwards [hn] with x hn
  let Zx:=ScalarCovarianceTailScale.observation (T:ℝ) x
  have hgapx:∀i,(c:ℝ)<(Zx i).target:=fun _=>by exact_mod_cast hcT
  let R:=FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Zx P hκP v c hgapx θ
  have hf:=FirstGammaAbsoluteReference.reference_absolute 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    Zx J P hκP hΛ v c hgapx hH (hT0.trans_le hTH) B hBDG hIJ₀ hIJ₁ θ hcH hvc.le
  have hp:=FirstGammaEndpointPhysical.value_eq_prefix 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    Zx J P hκP hΛ v T (fun _=>le_rfl) hTH θ c hgapx hH B hBDG hT0 hcT.le c le_rfl
  let A:=NativeFrozenSpatialObservation.row 𝓕 μ H T c v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hTH hcT.le x 0
  let D:=NativeFrozenSpatialObservation.row 𝓕 μ H T c v (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
    (FrozenReferenceFields.field P Λ κ θ hκP v (NativeCanonicalReferenceField.data OldU OldD))
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v _
      (NativeCanonicalReferenceField.data_measurable 𝓕 v OldU OldD OldUM OldDM)) hTH hcT.le x 0
  have he:StoppedItoInputs.stop 𝓕 μ H c (PastItoInputs.post 𝓕 μ H v (R (Fin.castAdd 1 0)))=
      TwoChannelItoRows.block 𝓕 μ H A D := by
    simp only [R,FirstGammaRows.replacement,Fin.append_left,PastFrozenPrefixRows.rows]
    rw [PastTwoChannelAlgebra.post_block,TwoChannelItoRows.stop_block]
    simp only [Zx,ScalarCovarianceTailScale.observation]
    rw [←NativeFrozenPrefixBridge.row_eq 𝓕 μ H T c v hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hTH hcT x]
    rw [←NativeFrozenPrefixBridge.row_eq 𝓕 μ H T c v (sub_pos.mpr hκP)
      (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
      (FrozenReferenceFields.field P Λ κ θ hκP v (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v))
      (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v _
        (MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)) hTH hcT x]
    rfl
  have hs:∀ᵐω∂μ,J.integral (StoppedItoInputs.stop 𝓕 μ H c (PastItoInputs.post 𝓕 μ H v (R (Fin.castAdd 1 0)))) ω=
      (leftIntegral 𝓕 μ H J).integral A ω+(rightIntegral 𝓕 μ H J).integral D ω:=by
    rw [he,TwoChannelItoRows.integral_block]
    exact Lp.coeFn_add _ _
  filter_upwards [hn,hf,hp,hs] with ω hn hf hp hs
  rw [hp]
  have hfi:=hf 0
  change FirstGammaAffine.reference 1 Λ θ (fun _=>(T:ℝ)) _ 0=_ at hfi
  rw [hfi]
  rw [hn,map_add,map_smul]
  change _=functional ((T:ℝ)-(v:ℝ)) x (S.first v ω)+
    (θ*Real.exp (-Λ*((T:ℝ)-(v:ℝ))))*functional ((T:ℝ)-(v:ℝ)) x (S.second v ω-S.first v ω)+
    (leftIntegral 𝓕 μ H J).integral A ω+(rightIntegral 𝓕 μ H J).integral D ω
  rw [hs]
  dsimp only [Zx,ScalarCovarianceTailScale.observation]
  ring

end SHE.FirstGammaCanonicalReference

