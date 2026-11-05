module

public import SHE.JointGammaReferenceNative
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

namespace SHE.JointGammaReferenceNativeTime
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

variable (hb1:(b:ℝ)≤1) (hc0:0<c) (hcb:c<b)
variable (hIJ0:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ1:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
local notation "State" θ=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP
  OldU OldD OldUM OldDM hbH hb1 I₀ I₁ θ
local notation "Curve" θ=>JointGammaReferenceCurve.curve 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
  I₀ I₁ u₀ v₀ S P hκP v b c hcH hc1 θ

include hc0 hcb hIJ0 hIJ1 hnull hBDG0 hBDG1 in
/-- The reference comparison holds on the TRUE original time/sample
product measure, with a genuine spatial-root event. This uses joint
Borel fields and Fubini, never an uncountable intersection of fixed-time
exceptional sets. -/
theorem reference_eq_curve_time (θ:ℝ):
    ∀ᵐ x:HeatCircle∂AddCircle.haarAddCircle,∀ᵐ p∂energyMeasure μ H,
      v<p.1→p.1<c→PredictableScalarField.nativeField (State θ) (p,x)=(Curve θ) (p,x):=by
  haveI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  have hb0:0<b:=hc0.trans hcb
  have hstate:Measurable (State θ):=
    ((NativeCanonicalReferenceField.state_predictable 𝓕 μ H b v P Λ κ hκ hκP
      OldU OldD OldUM OldDM hbH hb1 I₀ I₁ hb0 hnull B0 B1 hBDG0 hBDG1 θ).mono
        (predictable_le_product 𝓕)).measurable
  have hleft:Measurable (PredictableScalarField.nativeField (State θ)):=
    PredictableScalarField.nativeField_measurable hstate
  have hright:Measurable (Curve θ):=JointGammaReferenceCurve.curve_measurable 𝓕 μ H Λ κ hκ
    haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP v b c hcH hc1 hc0 hnull B0 B1 hBDG0 hBDG1 θ
  let Event:(ℝ≥0×Ω)×HeatCircle→Prop:=fun z=>v<z.1.1→z.1.1<c→
    PredictableScalarField.nativeField (State θ) z=(Curve θ) z
  have hm:MeasurableSet {z|Event z}:=by
    simp only [Event,imp_iff_not_or,not_lt,Set.ofPred_or]
    exact (measurableSet_le measurable_fst.fst measurable_const).union
      ((measurableSet_le measurable_const measurable_fst.fst).union
        (measurableSet_eq_fun hleft hright))
  have hfixed(q:ℝ≥0):∀ᵐ x:HeatCircle∂AddCircle.haarAddCircle,∀ᵐ ω∂μ,Event ((q,ω),x):=by
    by_cases hvq:v<q
    · by_cases hqc:q<c
      · exact (JointGammaReferenceNative.reference_eq_curve 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S J P hκP v b hbH c hcH hc1 hb1 q hvq hqc.le hc0 hcb
          hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1 θ).mono (fun x hx=>hx.mono (fun ω he _ _=>he))
      · exact ae_of_all _ (fun _=>ae_of_all _ (by simp [Event,hqc]))
    · exact ae_of_all _ (fun _=>ae_of_all _ (by simp [Event,hvq]))
  have htriple:∀ᵐ z∂(timeMeasure H).prod (μ.prod AddCircle.haarAddCircle),Event ((z.1,z.2.1),z.2.2):=by
    have hm3:MeasurableSet {z:ℝ≥0×(Ω×HeatCircle)|Event ((z.1,z.2.1),z.2.2)}:=
      hm.preimage ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
    apply (Measure.ae_prod_iff_ae_ae hm3).mpr
    apply ae_of_all
    intro q
    have hmq:MeasurableSet {z:Ω×HeatCircle|Event ((q,z.1),z.2)}:=
      hm.preimage ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hq:∀ᵐ ω∂μ,∀ᵐ x:HeatCircle∂AddCircle.haarAddCircle,Event ((q,ω),x):=
      (Measure.ae_ae_comm hmq).mpr (hfixed q)
    exact (Measure.ae_prod_iff_ae_ae hmq).mpr hq
  have hprod:∀ᵐ z∂(energyMeasure μ H).prod AddCircle.haarAddCircle,Event z:=
    (measurePreserving_prodAssoc (timeMeasure H) μ AddCircle.haarAddCircle).quasiMeasurePreserving.ae htriple
  exact (Measure.ae_ae_comm hm).mp (Measure.ae_ae_of_ae_prod hprod)
end SHE.JointGammaReferenceNativeTime
