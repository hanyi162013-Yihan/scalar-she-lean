module

public import SHE.MixedNativePastThetaMoments
public import SHE.MixedNativeEndpointLimit
public import SHE.ConditionalFatouMoment
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativeEndpointMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeEndpointMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeEndpointMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeEndpointMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeEndpointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeEndpointMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeEndpointMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))


open Filter Topology AddCircle
local instance mixedNativeEndpointMoments_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩

include hIJ₀ hIJ₁ in
/-- Actual zero-age physical current offsets satisfy the same sharp
conditional native leaf moment. ONE spatial event works for ALL F_v
events; the actual full-H integral and local age q-v are preserved. -/
theorem fractional_moment_on_past_event (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    {θ : ℝ} (hθ : |θ|≤1) (v q : ℝ≥0) (hvq : v<q) (hqH : q≤H)
    (hspan : (q:ℝ)-(v:ℝ)≤1) (p : ℕ) (hp : 0<p) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p J B) {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,∀ A : Set Ω,MeasurableSet[𝓕 v] A →
      Integrable (fun ω => |MixedNativeEndpointLimit.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        θ v q x ω|^(((2*p:ℕ):ℝ)*β)) (μ.restrict A) ∧
      (∫ ω in A,|MixedNativeEndpointLimit.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        θ v q x ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
      (NativeHybridMoments.momentConstant p B κ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2)*μ.real A := by
  obtain ⟨ε,hε,hε0,hlim⟩ := MixedNativeEndpointLimit.exists_offset_subsequence
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q hvq
  filter_upwards [hlim] with x hx
  intro A hA
  let f : ℕ → Ω → ℝ := fun n ω =>
    |MixedNativePastThetaMoments.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      θ v q ((q:ℝ)+ε n) x ω|^(((2*p:ℕ):ℝ)*β)
  let g : Ω → ℝ := fun ω =>
    |MixedNativeEndpointLimit.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      θ v q x ω|^(((2*p:ℕ):ℝ)*β)
  have hfg : ∀ᵐ ω ∂μ.restrict A,Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [ae_restrict_of_ae hx] with ω hω
    have hh := hω.abs.rpow_const (Or.inr (mul_nonneg (Nat.cast_nonneg (2*p)) hβ))
    simpa only [f,g,MixedNativePastThetaMoments.offset] using hh
  apply ConditionalFatouMoment.nonnegative_limit (μ.restrict A) f g hfg
    (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  · have hm : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
    apply mul_nonneg (mul_nonneg (Real.rpow_nonneg (by
      dsimp only [NativeHybridMoments.momentConstant]
      exact mul_nonneg B.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)) _)
      (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hvq.le)) _)) (measureReal_nonneg)
  · intro n
    exact MixedNativePastThetaMoments.fractional_moment_on_past_event
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ
      hlocal hΛ hθ v q hvq.le hqH hspan (lt_add_of_pos_right _ (hε n)) x p hp B hBDG A hA hβ hβ1

end SHE.MixedNativeEndpointMoments
