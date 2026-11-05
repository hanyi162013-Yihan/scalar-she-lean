module

public import SHE.MixedNativePastHybridIdentity
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

namespace SHE.MixedNativePastThetaCentering
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativePastThetaCentering_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativePastThetaCentering_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativePastThetaCentering_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativePastThetaCentering_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativePastThetaCentering_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativePastThetaCentering_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

/-- The actual individually stopped current coordinate. Original stop
sigma and heat target T remain independent. -/
def current (σ : ℝ) (q : ℝ≥0) (T : ℝ) (x : HeatCircle) (ω : Ω) : ℝ :=
  functional (T-(q:ℝ)) x (S.first q ω)+θ*Real.exp (-Λ*(σ-(q:ℝ)))*
    functional (T-(q:ℝ)) x (S.second q ω-S.first q ω)

def baseline (σ : ℝ) (v : ℝ≥0) (T : ℝ) (x : HeatCircle) (ω : Ω) : ℝ :=
  functional (T-(v:ℝ)) x (S.first v ω)+θ*Real.exp (-Λ*(σ-(v:ℝ)))*
    functional (T-(v:ℝ)) x (S.second v ω-S.first v ω)

theorem baseline_stronglyMeasurable (σ : ℝ) (v : ℝ≥0) (T : ℝ) (x : HeatCircle) :
    StronglyMeasurable[𝓕 v] (baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ σ v T x) := by
  have hU : StronglyMeasurable[𝓕 v] (S.first v) :=
    (show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v
  have hV : StronglyMeasurable[𝓕 v] (S.second v) :=
    (show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v
  exact ((functional (T-(v:ℝ)) x).continuous.comp_stronglyMeasurable hU).add
    (((functional (T-(v:ℝ)) x).continuous.comp_stronglyMeasurable (hV.sub hU)).const_mul _)

/-- For a literal native leaf sigma=T, the random-past baseline is
EXACTLY the printed controlled profile mean based on U_v,D_v. -/
theorem baseline_eq_profile (v : ℝ≥0) {T : ℝ} (hT : (v:ℝ)<T) (x : HeatCircle) (ω : Ω) :
    baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ T v T x ω=
      ControlledProfile.mean Λ (embed (S.first v ω)) (embed (S.second v ω-S.first v ω)) (θ,(T-(v:ℝ),x)) := by
  rw [baseline,functional_physical (sub_pos.mpr hT),functional_physical (sub_pos.mpr hT)]
  rfl

include hIJ₀ hIJ₁ in
/-- Actual random-past centered joint coordinate, integrated by the
same full-H hybrid input, with the true sigma-dependent damping. -/
theorem centered_current (hΛ : 0≤Λ) (hθ₀ : |θ|≤1) (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H)
    {σ T : ℝ} (hσ : (q:ℝ)≤σ) (hT : (q:ℝ)<T) (x : HeatCircle) :
    ∃ hθ : |θ*Real.exp (-Λ*(σ-(q:ℝ)))|≤1,
      (fun ω => current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ σ q T x ω-
        baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ σ v T x ω)=ᵐ[μ]
      J.integral (MixedNativePastHybridIdentity.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        v q hT x hΛ hθ) := by
  have he : |Real.exp (-Λ*(σ-(q:ℝ)))|≤1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (sub_nonneg.mpr hσ))
  have hθ : |θ*Real.exp (-Λ*(σ-(q:ℝ)))|≤1 := by
    rw [abs_mul]
    exact (mul_le_mul hθ₀ he (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  refine ⟨hθ,?_⟩
  have he := MixedNativePastHybridIdentity.centered_increment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ v q hvq hqH hT x hΛ hθ
  have hx : (θ*Real.exp (-Λ*(σ-(q:ℝ))))*Real.exp (-Λ*((q:ℝ)-(v:ℝ)))=θ*Real.exp (-Λ*(σ-(v:ℝ))) := by
    rw [mul_assoc,← Real.exp_add]
    congr 1
    ring
  filter_upwards [he] with ω hω
  change _=J.integral _ ω
  rw [current,baseline]
  rw [hx] at hω
  exact hω

end SHE.MixedNativePastThetaCentering
