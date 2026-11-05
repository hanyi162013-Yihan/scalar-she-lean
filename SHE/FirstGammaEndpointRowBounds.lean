module

public import SHE.FirstGammaEndpointMappedRows
public import SHE.NativeObservationCaps
public import SHE.FiniteReferenceSpliceRows
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaEndpointCovariance
public import SHE.FiniteAffineRows
public import SHE.PredictableRealSections
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaEndpointRowBounds
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointRowBounds_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointRowBounds_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointRowBounds_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointRowBounds_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointRowBounds_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointRowBounds_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointRowBounds_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointRowBounds_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open Set FiniteCovariancePullback
variable (θ : ℝ)
local notation "m0" => hell.le.trans ((hbU 0).1.trans (hbU 0).2)
local notation "Rows" => FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "R" => FirstGammaEndpointRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH
local notation "r0" => FirstGammaEndpointRows.additive 𝓕 μ H κ hκ Z b htarget hbH
local notation "rU" => FirstGammaEndpointRows.first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH
local notation "rV" => FirstGammaEndpointRows.second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH
local notation "L" => FirstGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "Ref" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)
local notation "C" => (1+StoppedFourier.heatConstant)

/-- Instantaneous physical current-row energy has NO exponential or
damping loss. The integrating-factor construction is only auxiliary. -/
theorem current_bound (hb1 : (b:ℝ)≤1) (hθ0 : 0≤θ) (hθ1 : θ≤1) :
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀ i,
      ‖mappedRow (L (p.1:ℝ)) (fun j=>Rows j p) i‖^2≤
        (κ+10*M)*C*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)) := by
  have h0 (i:Fin n):=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (htarget i) (Z i).center hbH hb1
  have hU (i:Fin n):=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b hell m0
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (htarget i) (Z i).center hbH hb1
  have hV (i:Fin n):=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b hell m0
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (htarget i) (Z i).center hbH hb1
  have hi (i:Fin n):=InterpolatedPredictableRows.interpolated_ae 𝓕 μ H hΛ b θ (r0 i) (rU i) (rV i)
  filter_upwards [FirstGammaEndpointMappedRows.current_rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ,
    ae_all_iff.mpr h0,ae_all_iff.mpr hU,ae_all_iff.mpr hV,ae_all_iff.mpr hi] with p hm h0 hU hV hi hvp hpb i
  rw [hm hvp hpb i]
  have he:=hi i hpb.le
  have he' : R (Fin.castAdd n i) p+ClippedExponential.coefficient Λ θ (p.1:ℝ) • R (Fin.natAdd n i) p=
      WithLp.toLp 2 (r0 i p,(1-θ) • rU i p+θ • rV i p):=by
    simpa only [FirstGammaEndpointRows.actual,Fin.append_left,Fin.append_right] using he
  rw [he',WithLp.prod_norm_sq_eq_of_L2]
  change ‖r0 i p‖^2+‖(1-θ) • rU i p+θ • rV i p‖^2≤_
  have hφ : 0≤((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)):=Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hpb.le)) _
  have hK : 0≤M*C*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)):=
    mul_nonneg (mul_nonneg m0 (add_nonneg zero_le_one StoppedFourier.heatConstant_pos.le)) hφ
  have hα : |1-θ|≤1:=abs_le.mpr ⟨by linarith,by linarith⟩
  have hd:=NativeObservationCaps.residual_bound (rU i p) (rV i p) hα hK (hU i hpb.le) (hV i hpb.le)
  have heq : (1-θ) • rU i p+θ • rV i p=rV i p+(1-θ) • (rU i p-rV i p):=by module
  rw [heq]
  have hz:=h0 i hpb.le
  change ‖r0 i p‖^2≤κ*C*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)) at hz
  nlinarith

/-- The actual mapped reference row has its true total-profile cap,
including the common additive variance and singular endpoint age. -/
theorem reference_bound (hb1 : (b:ℝ)≤1) :
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀ i,
      ‖mappedRow Ref (fun j=>Rows j p) i‖^2≤P.upper*C*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)) := by
  have hb (i:Fin n):=FirstGammaEndpointRows.replacement_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ hb1 (Fin.castAdd n i)
  filter_upwards [FirstGammaEndpointMappedRows.reference_rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ,
    ae_all_iff.mpr hb] with p hr hb hvp hpb i
  rw [hr hvp hpb i]
  simpa only [FirstGammaEndpointRows.replacement,FirstGammaEndpointRows.replacementCap,Fin.append_left] using hb i hpb.le

end SHE.FirstGammaEndpointRowBounds
