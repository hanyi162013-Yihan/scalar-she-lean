module

public import SHE.JointGammaReferenceTime
public import SHE.JointGammaReferenceNativeTime
public import SHE.PositivePrefixAE
public import SHE.JointGammaReferencePrefix
public import SHE.AEContinuousVersion
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

namespace SHE.JointGammaNativeReferenceTime
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaNativeReferenceTime_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaNativeReferenceTime_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaNativeReferenceTime_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaNativeReferenceTime_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaNativeReferenceTime_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaNativeReferenceTime_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaNativeReferenceTime_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaNativeReferenceTime_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance jointGammaNativeReferenceTime_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaNativeReferenceTime_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaNativeReferenceTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaNativeReferenceTime_realSecond : SecondCountableTopology RealL2:=
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

local notation "hb1"=>(show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
local notation "State" θ=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP
  OldU OldD OldUM OldDM hbH hb1 I₀ I₁ θ
attribute [local irreducible] functional FirstGammaEndpointConstruction.value NativeCanonicalReferenceField.state

include hH B hBDG hIJ₀ hIJ₁ hcH hc1 in
theorem reference_eq_field_prefix (hc0:0<c) (hcb:c<b)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (θ:ℝ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐp∂energyMeasure μ H,v<p.1→p.1<c→
      FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ))
        (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ p) 0=
      PredictableScalarField.nativeField (State θ) (p,x):=by
  have hn:=JointGammaReferenceNativeTime.reference_eq_curve_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J P hκP v b hbH c hcH hc1 hb1 hc0 hcb hIJ₀ hIJ₁ hnull B0 B1 hBDG0 hBDG1 θ
  filter_upwards [hn] with x hx
  filter_upwards [hx,JointGammaReferenceTime.reference_eq_curve_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J P hκP hΛ v b hbH c hcH hc1 hH B hBDG hIJ₀ hIJ₁
    hc0 hcb hnull B0 B1 hBDG0 hBDG1 θ x] with p hn hf hvp hpc
  exact (hf hvp hpc).trans (hn hvp hpc).symm

include hH B hBDG hIJ₀ hIJ₁ in
/-- The exact finite ORIGINAL-J frozen reference equals the jointly
predictable native field on the FULL strict time window and native-root
product event, using a countable positive-prefix exhaustion. -/
theorem reference_eq_field_time (hb0:0<b)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (θ:ℝ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐp∂energyMeasure μ H,v<p.1→p.1<b→
      FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ))
        (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ p) 0=
      PredictableScalarField.nativeField (State θ) (p,x):=by
  apply PositivePrefixAE.exhaust AddCircle.haarAddCircle (energyMeasure μ H) v b hb0 Prod.fst
  intro c hc0 hcb
  exact reference_eq_field_prefix 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J P hκP hΛ v b hbH
    c (hcb.le.trans hbH) ((show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb.le).trans hb1)
    hH B hBDG hIJ₀ hIJ₁ hc0 hcb hnull B0 B1 hBDG0 hBDG1 θ

end SHE.JointGammaNativeReferenceTime
