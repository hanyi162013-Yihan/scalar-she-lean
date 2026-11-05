module

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

namespace SHE.JointGammaReferenceTime
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaReferenceTime_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaReferenceTime_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaReferenceTime_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaReferenceTime_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaReferenceTime_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaReferenceTime_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaReferenceTime_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaReferenceTime_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance jointGammaReferenceTime_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaReferenceTime_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaReferenceTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaReferenceTime_realSecond : SecondCountableTopology RealL2:=
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

attribute [local irreducible] functional FirstGammaEndpointConstruction.value JointGammaReferenceCurve.curve
include hH B hBDG hIJ₀ hIJ₁ in
/-- For EVERY native root the actual finite reference is its bounded
prefix curve on the genuine original time/sample measure. -/
theorem reference_eq_curve_time (hc0:0<c) (hcb:c<b)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (θ:ℝ) (x:HeatCircle):
    ∀ᵐp∂energyMeasure μ H,v<p.1→p.1<c→
      FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ))
        (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ p) 0=
      (Curve θ) (p,x):=by
  let u:ℝ≥0→Ω→ℝ:=fun q ω=>FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ))
    (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ (q,ω)) 0
  let f:ℝ≥0×Ω→ℝ:=fun p=>(Curve θ) (p,x)
  have hf:Measurable f:=(JointGammaReferenceCurve.curve_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S P hκP v b c hcH hc1 hc0 hnull B0 B1 hBDG0 hBDG1 θ).comp
      (measurable_id.prodMk measurable_const)
  have hu(ω:Ω):Continuous (fun q:Set.Ioo v c=>u q ω):=by
    have hY:=FirstGammaEndpointConstruction.continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b
      (fun _=>le_rfl) hbH θ (hc0.trans hcb) ω
    exact (EuclideanSpace.proj (0:Fin 1)).continuous.comp
      ((FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ))).continuous.comp
        (hY.comp continuous_subtype_val))
  have hs(q:ℝ≥0)(hq:q∈Set.Ioo v c):u q=ᵐ[μ] fun ω=>f (q,ω):=
    JointGammaReferencePrefix.reference_eq_curve 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S J P hκP hΛ v b hbH c hcH hc1 hH B hBDG hIJ₀ hIJ₁
      hc0 hcb q hq.1 hq.2.le B0 B1 hBDG0 hBDG1 θ x
  have he:=AEContinuousSections.ae_eq_version_on (timeMeasure H) μ (Set.Ioo v c) measurableSet_Ioo u f hu hf hs
  rw [Measure.restrict_prod_eq_prod_univ] at he
  exact (ae_imp_of_ae_restrict he).mono (fun p hp hvp hpc=>hp ⟨⟨hvp,hpc⟩,Set.mem_univ _⟩)

end SHE.JointGammaReferenceTime
