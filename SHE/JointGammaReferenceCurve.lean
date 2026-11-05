module

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

namespace SHE.JointGammaReferenceCurve
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
attribute [local irreducible] functional

/-- A genuine positive-prefix scalar curve for the canonical frozen
reference, retaining its ORIGINAL full-target old damping. -/
def curve (θ:ℝ) (p:(ℝ≥0×Ω)×HeatCircle):ℝ:=
  functional ((b:ℝ)-(v:ℝ)) p.2
    (OldU p.1.2+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • OldD p.1.2)+
    (N1 θ) p+N0 p

theorem curve_continuous (hc0:0<c) (θ:ℝ) (ω:Ω) (x:HeatCircle):
    Continuous (fun q=>curve 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP v b c hcH hc1 θ ((q,ω),x)):=by
  unfold curve
  exact ((continuous_const (y:=functional ((b:ℝ)-(v:ℝ)) x
    (OldU ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • OldD ω))).add (NativeFrozenPrefixCurve.continuous_scalar 𝓕 μ H
    (sub_pos.mpr hκP) Mres (Fres θ) (FresM θ) b c v hcH hc1 I₁ hc0 ω x)).add
      (NativeFrozenPrefixCurve.continuous_scalar 𝓕 μ H hκ hκ.le
        (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const b c v hcH hc1 I₀ hc0 ω x)

theorem curve_measurable (hc0:0<c) (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (θ:ℝ):
    Measurable (curve 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP v b c hcH hc1 θ):=by
  unfold curve
  have hu:Measurable OldU:=(OldUM).mono (𝓕.le v) le_rfl
  have hd:Measurable OldD:=(OldDM).mono (𝓕.le v) le_rfl
  have hinit:Measurable (fun p:(ℝ≥0×Ω)×HeatCircle=>functional ((b:ℝ)-(v:ℝ)) p.2
      (OldU p.1.2+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • OldD p.1.2)):=
    observable_measurable
      ((hu.add (hd.const_smul (θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))))).comp measurable_fst.snd)
      (measurable_const (a:=(b:ℝ)-(v:ℝ))) measurable_snd
  exact (hinit.add (NativeFrozenPrefixCurve.scalar_measurable 𝓕 μ H
    (sub_pos.mpr hκP) Mres (Fres θ) (FresM θ) b c v hcH hc1 I₁ hc0 hnull B1 hBDG1)).add
      (NativeFrozenPrefixCurve.scalar_measurable 𝓕 μ H hκ hκ.le
        (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const b c v hcH hc1 I₀ hc0 hnull B0 hBDG0)

end SHE.JointGammaReferenceCurve
