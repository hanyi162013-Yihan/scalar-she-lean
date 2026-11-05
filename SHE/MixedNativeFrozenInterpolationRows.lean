module

public import SHE.MixedNativeFrozenPrefixIto
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeFrozenInterpolationRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance mixedNativeFrozenInterpolationRows_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeFrozenInterpolationRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeFrozenInterpolationRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeFrozenInterpolationRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeFrozenInterpolationRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeFrozenInterpolationRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeFrozenInterpolationRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeFrozenInterpolationRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open MixedNativeFrozenPrefixIto
variable (θ : ℝ)

def ordinaryRows (i : Fin n) : Process (E:=Both RealHaarInput) 𝓕 μ H :=
  MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S c (hgap i) (Z i).center

theorem ordinaryRows_bound (i : Fin n) :
    ∀ᵐ p ∂energyMeasure μ H,‖ordinaryRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap i p‖^2≤
      NativeObservationCaps.cap (κ+M) ((Z i).target-(c:ℝ)) := by
  have hm : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have h0 := NativeObservationCaps.process_bound 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (hgap i) (Z i).center
  have h1 := NativeObservationCaps.process_bound 𝓕 μ H hell hm
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (hgap i) (Z i).center
  filter_upwards [NativeObservationCaps.block_bound 𝓕 μ H _ _ h0 h1] with p hp
  exact hp.trans_eq (by unfold NativeObservationCaps.cap;ring)

/-- Actual interpolation covers both first-Gamma endpoints theta=0,1
and every intermediate controlled current, on the original drivers. -/
def currentRows (i : Fin n) : Process (E:=Both RealHaarInput) 𝓕 μ H :=
  (1-θ) • ordinaryRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap i+
    θ • actualRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap i

def frozenRows (i : Fin n) : Process (E:=Both RealHaarInput) 𝓕 μ H :=
  PastFrozenPrefixRows.rows 𝓕 μ H P Λ κ θ hκ hκP v
    (data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
    (data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) Z c hgap i

def initial : WordRecursion.State n :=
  (1-θ) • PositiveGapObservations.initial Z u₀+
    θ • MixedNativeJointObservations.initial Λ u₀ v₀ Z

theorem initial_apply (i : Fin n) :
    initial Λ u₀ v₀ Z θ i=functional (Z i).target (Z i).center u₀+
      θ*Real.exp (-Λ*(Z i).stop)*functional (Z i).target (Z i).center (v₀-u₀) := by
  simp only [initial,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    PositiveGapObservations.initial,WithLp.ofLp_toLp,MixedNativeJointObservations.initial_apply]
  ring

theorem currentRows_bound (hθ0 : 0≤θ) (hθ1 : θ≤1)
    (hstop : ∀ i,(c:ℝ)≤(Z i).stop) (i : Fin n) :
    ∀ᵐ p ∂energyMeasure μ H,‖currentRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap θ i p‖^2≤
      NativeObservationCaps.cap (4*κ+22*M) ((Z i).target-(c:ℝ)) := by
  let U := ordinaryRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap i
  let V := actualRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap i
  filter_upwards [ordinaryRows_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap i,
    MixedNativeJointCaps.clippedRows_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap hstop i,
    ae_eq_of_ae_eq_trim (Lp.coeFn_add ((1-θ) • U) (θ • V)),
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul (1-θ) U),ae_eq_of_ae_eq_trim (Lp.coeFn_smul θ V)]
    with p hu hv ha hsu hsv
  change ‖((1-θ) • U+θ • V) p‖^2≤_
  rw [ha]
  simp only [Pi.add_apply,hsu,hsv,Pi.smul_apply]
  change ‖U p‖^2≤NativeObservationCaps.cap (κ+M) ((Z i).target-(c:ℝ)) at hu
  change ‖V p‖^2≤NativeObservationCaps.cap (κ+10*M) ((Z i).target-(c:ℝ)) at hv
  have hα : |1-θ|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hθ : |θ|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hnU : ‖(1-θ) • U p‖≤‖U p‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hα (norm_nonneg _)).trans_eq (one_mul _)
  have hnV : ‖θ • V p‖≤‖V p‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hθ (norm_nonneg _)).trans_eq (one_mul _)
  have hpowU := pow_le_pow_left₀ (norm_nonneg _) hnU 2
  have hpowV := pow_le_pow_left₀ (norm_nonneg _) hnV 2
  have hn := (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le ((1-θ) • U p) (θ • V p)) 2).trans
    (add_pow_le (norm_nonneg _) (norm_nonneg _) 2)
  have hb : ‖(1-θ) • U p+θ • V p‖^2≤
      2*(NativeObservationCaps.cap (κ+M) ((Z i).target-(c:ℝ))+
        NativeObservationCaps.cap (κ+10*M) ((Z i).target-(c:ℝ))) := by
    norm_num only at hn
    linarith
  exact hb.trans_eq (by unfold NativeObservationCaps.cap;ring)

end SHE.MixedNativeFrozenInterpolationRows
