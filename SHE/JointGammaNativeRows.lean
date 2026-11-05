module

public import SHE.NativePhysicalGammaKernel
public import SHE.NativeEndpointRowCast
public import SHE.NativePhysicalRowCongruence
public import SHE.MixedNativeGammaEnergy
public import SHE.NativeCanonicalGammaEnergy
public import SHE.JointGammaReferenceCurve
public import SHE.NativeFrozenPrefixCurve
public import SHE.NativeObservableFields
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

namespace SHE.JointGammaNativeRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaReferenceCurve_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaReferenceCurve_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaReferenceCurve_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaReferenceCurve_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaReferenceCurve_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaReferenceCurve_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaReferenceCurve_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaReferenceCurve_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance jointGammaReferenceCurve_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaReferenceCurve_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaReferenceCurve_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaReferenceCurve_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local notation "Lower"=>MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Upper"=>MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ)
local notation "LowerPos"=>MixedNativeGammaEnergy.commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)
local notation "CurrentU"=>MixedNativeGammaEnergy.currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "CurrentV"=>MixedNativeGammaEnergy.currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "Frozen"=>(fun θ:ℝ=>NativeCanonicalGammaEnergy.frozen (v:=v)
  (U:=Function.uncurry S.first) (V:=Function.uncurry S.second)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (m:=Lower) (W:=Upper)
  (hmP:=min_le_right _ _) (hWP:=le_max_right _ _) θ)
local notation "Obs" x=>ScalarCovarianceTailScale.observation b x
local notation "rA" x:max=>FirstGammaEndpointRows.additive 𝓕 μ H κ hκ (Obs x) b (fun _=>le_rfl) hbH 0
local notation "rU" x:max=>FirstGammaEndpointRows.first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  (Obs x) b (fun _=>le_rfl) hbH 0
local notation "rV" x:max=>FirstGammaEndpointRows.second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  (Obs x) b (fun _=>le_rfl) hbH 0
local notation "rF"=>(fun (θ:ℝ)(x:HeatCircle)=>FirstGammaEndpointRows.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  (Obs x) P hκP v b (fun _=>le_rfl) hbH θ 0)

/-- Literal additive row on the SAME original full-H input. -/
theorem additive (x:HeatCircle):∀ᵐ p∂energyMeasure μ H,p.1<b→
    (rA x) p=NativeObservationCovariance.row hκ (AdditiveHaarForcing.constantField κ hκ) b p.1 x:=by
  simpa only [FirstGammaEndpointRows.additive,ScalarCovarianceTailScale.observation] using
    NativeObservationCovariance.endpoint_row_cast 𝓕 μ H b hκ hκ.le hκ
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
      (fun _=>AdditiveHaarForcing.constantField κ hκ) (fun _=>rfl) hbH x

/-- The genuine U row is unchanged by the common ellipticity cast. -/
theorem first (x:HeatCircle):∀ᵐ p∂energyMeasure μ H,p.1<b→
    (rU x) p=NativeObservationCovariance.row LowerPos (CurrentU p) b p.1 x:=by
  simpa only [FirstGammaEndpointRows.first,ScalarCovarianceTailScale.observation] using
    NativeObservationCovariance.endpoint_row_cast 𝓕 μ H b hell
      (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) LowerPos
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient CurrentU
      (fun _=>rfl) hbH x

/-- The genuine V row uses the SAME common window, without changing
its actual nonlinear coefficient. -/
theorem second (x:HeatCircle):∀ᵐ p∂energyMeasure μ H,p.1<b→
    (rV x) p=NativeObservationCovariance.row LowerPos (CurrentV p) b p.1 x:=by
  simpa only [FirstGammaEndpointRows.second,ScalarCovarianceTailScale.observation] using
    NativeObservationCovariance.endpoint_row_cast 𝓕 μ H b hell
      (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) LowerPos
      (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient CurrentV
      (fun _=>rfl) hbH x

/-- The actual own-profile frozen row equals its literal physical row,
with exact random old states and unchanged original profile. -/
theorem frozen (θ:ℝ)(x:HeatCircle):∀ᵐ p∂energyMeasure μ H,p.1<b→
    (rF θ x) p=NativeObservationCovariance.row LowerPos (Frozen θ p) b p.1 x:=by
  simpa only [FirstGammaEndpointRows.frozen,ScalarCovarianceTailScale.observation] using
    NativeObservationCovariance.endpoint_row_cast 𝓕 μ H b (sub_pos.mpr hκP)
      (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) LowerPos
      (FrozenReferenceFields.field P Λ κ θ hκP v
        (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v))
      (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v _
        (MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v))
      (Frozen θ) (fun _=>rfl) hbH x

/-- Both channels of the literal current block match the physical
kernel, for every spatial root on original time/sample measure. -/
theorem current_block (x:HeatCircle):∀ᵐ p∂energyMeasure μ H,p.1<b→
    WithLp.toLp 2 ((rA x) p,(rU x) p)=NativePhysicalGammaKernel.block b hκ LowerPos (CurrentU p) p x:=by
  filter_upwards [additive 𝓕 μ H κ hκ b hbH x,first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP b hbH x]
    with p hA hU hpb
  rw [hA hpb,hU hpb]
  rfl
end SHE.JointGammaNativeRows
