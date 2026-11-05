module

public import SHE.FirstGammaEndpointRows
public import SHE.FullHorizonCovariance
public import SHE.PastFrozenPrefixCovariance
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

namespace SHE.FirstGammaEndpointCovariance
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointCovariance_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointCovariance_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open Set CovarianceMatrix
variable (θ : ℝ)
local notation "Past" => MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "hPast" => MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "r0" => FirstGammaEndpointRows.additive 𝓕 μ H κ hκ Z b htarget hbH
local notation "rF" => FirstGammaEndpointRows.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ
local notation "f0" => fun _ : ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ
local notation "fF" => FrozenReferenceFields.field P Λ κ θ hκP v Past

/-- Literal full-H additive/frozen rows have the actual TOTAL random
canonical covariance on the whole window, including zero terminal gap. -/
theorem frozen_covariance :
    ∀ᵐ ω∂μ,∀ᵐ t:ℝ∂volume.restrict (Ioc (v:ℝ) (b:ℝ)),
      StandardFiniteIto.rowCovariance 𝓕 μ H (fun i=>TwoChannelItoRows.block 𝓕 μ H (r0 i) (rF i)) ω t=
        densityMatrix (ControlledReferenceWindows.coefficient P Λ θ v (Past ω)) Z t := by
  have hsum:=TwoChannelItoRows.rowCovariance_sum_ae_real 𝓕 μ H r0 rF
  have h0:=FullHorizonCovariance.rowCovariance_eq_density 𝓕 μ H b hκ hκ.le f0 stronglyMeasurable_const Z htarget hbH
  have hF:=FullHorizonCovariance.rowCovariance_eq_density 𝓕 μ H b (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) fF
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v Past hPast) Z htarget hbH
  have hsH : Ioc (v:ℝ) (b:ℝ)⊆Ioc (0:ℝ) (H:ℝ):=fun t ht=>⟨v.2.trans_lt ht.1,ht.2.trans (by exact_mod_cast hbH)⟩
  have hsb : Ioc (v:ℝ) (b:ℝ)⊆Ioc (0:ℝ) (b:ℝ):=fun t ht=>⟨v.2.trans_lt ht.1,ht.2⟩
  filter_upwards [hsum,h0,hF] with ω hsum h0 hF
  filter_upwards [hsum.filter_mono (ae_mono (Measure.restrict_mono_set volume hsH)),
    h0.filter_mono (ae_mono (Measure.restrict_mono_set volume hsb)),
    hF.filter_mono (ae_mono (Measure.restrict_mono_set volume hsb)),
    ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t hsum h0 hF ht hne
  rw [hsum]
  change StandardFiniteIto.rowCovariance 𝓕 μ H r0 ω t=_ at h0
  change StandardFiniteIto.rowCovariance 𝓕 μ H rF ω t=_ at hF
  rw [h0,hF]
  have ht0 : 0≤t:=v.2.trans ht.1.le
  have htb : t<(b:ℝ):=lt_of_le_of_ne ht.2 hne
  have hδ : 0<(b:ℝ)-t:=sub_pos.mpr htb
  have hg : ∀ i,(b:ℝ)-t≤(Z i).target-(t.toNNReal:ℝ):=by
    intro i
    rw [Real.coe_toNNReal _ ht0]
    exact sub_le_sub_right (htarget i) _
  exact PastFrozenPrefixCovariance.density_sum_eq P Λ κ θ hκ hκP v Past Z t.toNNReal
    ht.1 (by rw [Real.coe_toNNReal _ ht0]) ω hδ hg

end SHE.FirstGammaEndpointCovariance
