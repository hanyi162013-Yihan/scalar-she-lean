module

public import SHE.PastEventWeights
public import SHE.MixedNativePastThetaMoments
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

namespace SHE.MixedNativePastWeightedMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativePastWeightedMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativePastWeightedMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativePastWeightedMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativePastWeightedMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativePastWeightedMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativePastWeightedMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

open PastItoInputs PastItoAlgebra PhysicalProfile

variable (θ : ℝ)

/-- The actual random-reference native leaf offset is Borel in the
original probability variable. Its profile mean is identified through
the genuine past-state baseline, rather than an independent restart. -/
theorem offset_measurable (v q : ℝ≥0) (hvq : v≤q) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    Measurable (MixedNativePastThetaMoments.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x) := by
  have hcurrent := (MixedNativePastThetaCentering.baseline_stronglyMeasurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ T q T x).measurable.mono (𝓕.le q) le_rfl
  have hbase := (MixedNativePastThetaCentering.baseline_stronglyMeasurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ T v T x).measurable.mono (𝓕.le v) le_rfl
  have he : MixedNativePastThetaMoments.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x=
      fun ω=>MixedNativePastThetaCentering.baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ T q T x ω-
        MixedNativePastThetaCentering.baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ T v T x ω := by
    funext ω
    rw [MixedNativePastThetaMoments.offset,←MixedNativePastThetaCentering.baseline_eq_profile
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v
        (lt_of_le_of_lt (by exact_mod_cast hvq) hT) x ω]
    rfl
  rw [he]
  exact hcurrent.sub hbase

include hIJ₀ hIJ₁ in
/-- The exact conditional native leaf gain survives multiplication by
ANY nonnegative integrable past-measurable input energy. The input can
be correlated with the current mean, covariance and every later word. -/
theorem fractional_moment_with_past_weight (hlocal : StandardTerminalPastLocality J)
    (hΛ : 0≤Λ) (hθ : |θ|≤1) (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H)
    (hspan : (q:ℝ)-(v:ℝ)≤1) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1)
    (g : Ω→ℝ) (hg : Measurable[𝓕 v] g) (hg0 : ∀ ω,0≤g ω) (hgi : Integrable g μ) :
    Integrable (fun ω=>g ω*|MixedNativePastThetaMoments.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x ω|^
        (((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,g ω*|MixedNativePastThetaMoments.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x ω|^
        (((2*p:ℕ):ℝ)*β) ∂μ)≤
      (NativeHybridMoments.momentConstant p B κ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2)*(∫ ω,g ω ∂μ) := by
  let f := fun ω=>|MixedNativePastThetaMoments.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x ω|^(((2*p:ℕ):ℝ)*β)
  have hm : Measurable f := (continuous_abs.measurable.comp
    (offset_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q hvq hT x)).pow_const _
  have he (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :=
    MixedNativePastThetaMoments.fractional_moment_on_past_event 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ hlocal hΛ hθ v q hvq hqH hspan hT x p hp B hBDG A hA hβ hβ1
  have hi : Integrable f μ := by
    simpa only [Measure.restrict_univ] using (he Set.univ MeasurableSet.univ).1
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hK : 0≤(NativeHybridMoments.momentConstant p B κ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2) := by
    apply mul_nonneg
    · apply Real.rpow_nonneg
      unfold NativeHybridMoments.momentConstant
      exact mul_nonneg B.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)
    · exact Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hvq)) _
  exact PastEventWeights.weighted_integral μ (𝓕.le v) f hm hi
    (fun _=>Real.rpow_nonneg (abs_nonneg _) _) _ hK (fun A hA=>(he A hA).2) g hg hg0 hgi

end SHE.MixedNativePastWeightedMoments
