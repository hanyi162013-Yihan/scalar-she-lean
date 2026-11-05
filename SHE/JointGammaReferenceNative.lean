module

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

namespace SHE.JointGammaReferenceNative
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

variable (hb1:(b:ℝ)≤1) (q:ℝ≥0) (hvq:v<q) (hqc:q≤c) (hc0:0<c) (hcb:c<b)
variable (hIJ0:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ1:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)

include hvq hqc hc0 hcb hIJ0 hIJ1 hnull hBDG0 hBDG1 in
/-- The canonical native own-profile reference is the SAME genuine
positive-prefix scalar curve, on a true spatial-root/sample event.
Full target b and partial current q remain distinct. -/
theorem reference_eq_curve (θ:ℝ):
    ∀ᵐ x:HeatCircle∂AddCircle.haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField
        (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP
          OldU OldD OldUM OldDM hbH hb1 I₀ I₁ θ (q,ω)) (ω,x)=
      JointGammaReferenceCurve.curve 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hκP v b c hcH hc1 θ ((q,ω),x):=by
  have hb0:0<b:=hc0.trans hcb
  let Init:Ω→RealL2:=NativeCanonicalReferenceField.initial (b:=b) (v:=v) (Λ:=Λ)
    (u:=OldU) (d:=OldD) θ
  let Rnoise:Ω→RealL2:=fun ω=>NativeFrozenHilbertField.noise 𝓕 μ H b v
    (sub_pos.mpr hκP) Mres (Fres θ) (FresM θ) hbH hb1 I₁ q ω
  let Anoise:Ω→RealL2:=fun ω=>NativeFrozenHilbertField.noise 𝓕 μ H b v
    hκ hκ.le (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 I₀ q ω
  have hi:Measurable Init:=
    (NativeCanonicalReferenceField.initial_measurable (𝓕:=𝓕) (v:=v) (b:=b) (Λ:=Λ)
      (u:=OldU) (d:=OldD) (hu:=OldUM) (hd:=OldDM) θ).mono (𝓕.le v) le_rfl
  have hr:Measurable Rnoise:=
    (((NativeFrozenHilbertField.noise_predictable 𝓕 μ H b v (sub_pos.mpr hκP) Mres
      (Fres θ) (FresM θ) hbH hb1 I₁ hb0 hnull B1 hBDG1).mono
        (predictable_le_product 𝓕)).measurable).comp (measurable_const.prodMk measurable_id)
  have ha:Measurable Anoise:=
    (((NativeFrozenHilbertField.noise_predictable 𝓕 μ H b v hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 I₀
        hb0 hnull B0 hBDG0).mono (predictable_le_product 𝓕)).measurable).comp
          (measurable_const.prodMk measurable_id)
  have hsum1:=NativeScalarProductAlgebra.add_ae μ Init Rnoise hi hr
  have hsum2:=NativeScalarProductAlgebra.add_ae μ (fun ω=>Init ω+Rnoise ω) Anoise (hi.add hr) ha
  have hheat:=NativeScalarProductAlgebra.heat_ae μ
    (fun ω=>OldU ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • OldD ω)
    (((OldUM).mono (𝓕.le v) le_rfl).add
      (((OldDM).mono (𝓕.le v) le_rfl).const_smul (θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))))
    (sub_pos.mpr (show (v:ℝ)<(b:ℝ) by exact_mod_cast hvq.trans_le (hqc.trans hcb.le)))
  have hn1:=NativeFrozenPrefixObservation.noise_native 𝓕 μ H (sub_pos.mpr hκP) Mres
    (Fres θ) (FresM θ) b c q v hbH hb1 hc0 hcb hqc I₁ (rightIntegral 𝓕 μ H J)
      hIJ1 hnull B1 hBDG1
  have hn0:=NativeFrozenPrefixObservation.noise_native 𝓕 μ H hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const b c q v
      hbH hb1 hc0 hcb hqc I₀ (leftIntegral 𝓕 μ H J) hIJ0 hnull B0 hBDG0
  filter_upwards [hsum1,hsum2,hheat,hn1,hn0] with x hsum1 hsum2 hheat hn1 hn0
  filter_upwards [hsum1,hsum2,hheat,hn1,hn0] with ω hsum1 hsum2 hheat hn1 hn0
  have he:NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP
      OldU OldD OldUM OldDM hbH hb1 I₀ I₁ θ (q,ω)=(Init ω+Rnoise ω)+Anoise ω:=by
    simp only [NativeCanonicalReferenceField.state,NativeFrozenHilbertField.field,
      PredictablePastParameter.held_eq (p:=(q,ω)) _ _ hvq]
    rfl
  rw [NativeScalarFieldAlgebra.congr _ (fun ω=>(Init ω+Rnoise ω)+Anoise ω) ω he x,
    hsum2,hsum1]
  change PredictableScalarField.nativeField (fun ω=>heat ((b:ℝ)-(v:ℝ))
      (OldU ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • OldD ω)) (ω,x)+
    PredictableScalarField.nativeField Rnoise (ω,x)+PredictableScalarField.nativeField Anoise (ω,x)=_
  rw [hheat,hn1,hn0]
  rfl
end SHE.JointGammaReferenceNative
