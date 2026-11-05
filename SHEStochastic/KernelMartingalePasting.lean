module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.KernelMartingalePasting
open MeasureTheory ProbabilityTheory

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  (μ : Measure Ω) [SFinite μ] (κ : Kernel Ω Y) [IsMarkovKernel κ]

/-- Kernel pasting works in any real Banach space. This covers complex
characteristic martingales and finite-dimensional vector coordinates. -/
theorem cylinder_identity_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (test : Ω × Y → ℝ) (post : Ω × Y → E) (pre : Ω → E) (originalTest : Ω → ℝ)
    (hpre : ∀ z : Ω × Y, pre z.1 ≠ 0 → test z = originalTest z.1)
    (hipre : Integrable (fun z : Ω × Y ↦ test z • pre z.1) (μ ⊗ₘ κ))
    (hipost : Integrable (fun z : Ω × Y ↦ test z • post z) (μ ⊗ₘ κ))
    (hpre_zero : (∫ ω, originalTest ω • pre ω ∂μ) = 0)
    (hpost_zero : ∀ᵐ ω ∂μ, (∫ y, test (ω, y) • post (ω, y) ∂κ ω) = 0) :
    (∫ z, test z • (pre z.1 + post z) ∂(μ ⊗ₘ κ)) = 0 := by
  have he (z : Ω × Y) : test z • pre z.1 = originalTest z.1 • pre z.1 := by
    by_cases hz : pre z.1 = 0
    · simp only [hz, smul_zero]
    · rw [hpre z hz]
  calc
    _ = (∫ z, test z • pre z.1 ∂(μ ⊗ₘ κ)) + ∫ z, test z • post z ∂(μ ⊗ₘ κ) := by
      simp_rw [smul_add]
      exact integral_add hipre hipost
    _ = (∫ ω, originalTest ω • pre ω ∂μ) + ∫ ω, ∫ y, test (ω, y) • post (ω, y) ∂κ ω ∂μ := by
      rw [Measure.integral_compProd hipre, Measure.integral_compProd hipost]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        simp only [he, integral_const, probReal_univ, one_smul]
    _ = 0 := by rw [hpre_zero, integral_congr_ae hpost_zero, integral_zero, add_zero]

/-- The Banach-valued increment split may hold only almost surely. -/
theorem cylinder_identity_smul_of_split {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (increment : Ω × Y → E) (test : Ω × Y → ℝ) (post : Ω × Y → E)
    (pre : Ω → E) (originalTest : Ω → ℝ)
    (hsplit : increment =ᵐ[μ ⊗ₘ κ] fun z ↦ pre z.1 + post z)
    (hpre : ∀ z : Ω × Y, pre z.1 ≠ 0 → test z = originalTest z.1)
    (hipre : Integrable (fun z : Ω × Y ↦ test z • pre z.1) (μ ⊗ₘ κ))
    (hipost : Integrable (fun z : Ω × Y ↦ test z • post z) (μ ⊗ₘ κ))
    (hpre_zero : (∫ ω, originalTest ω • pre ω ∂μ) = 0)
    (hpost_zero : ∀ᵐ ω ∂μ, (∫ y, test (ω, y) • post (ω, y) ∂κ ω) = 0) :
    (∫ z, test z • increment z ∂(μ ⊗ₘ κ)) = 0 :=
  (integral_congr_ae (hsplit.mono fun z hz ↦ congrArg (fun v ↦ test z • v) hz)).trans
    (cylinder_identity_smul μ κ test post pre originalTest hpre hipre hipost hpre_zero hpost_zero)

/-- The original stopped-martingale increment is multiplied by an
original past test wherever it is nonzero. The conditional future
martingale cancels under each continuation law. Fubini then proves the
actual cylinder-test identity on the enlarged probability space. -/
theorem cylinder_identity (test post : Ω × Y → ℝ) (pre originalTest : Ω → ℝ)
    (hpre : ∀ z : Ω × Y, pre z.1 ≠ 0 → test z = originalTest z.1)
    (hipre : Integrable (fun z : Ω × Y ↦ test z * pre z.1) (μ ⊗ₘ κ))
    (hipost : Integrable (fun z : Ω × Y ↦ test z * post z) (μ ⊗ₘ κ))
    (hpre_zero : (∫ ω, originalTest ω * pre ω ∂μ) = 0)
    (hpost_zero : ∀ᵐ ω ∂μ, (∫ y, test (ω, y) * post (ω, y) ∂κ ω) = 0) :
    (∫ z, test z * (pre z.1 + post z) ∂(μ ⊗ₘ κ)) = 0 := by
  simpa only [smul_eq_mul] using
    cylinder_identity_smul μ κ test post pre originalTest hpre hipre hipost hpre_zero hpost_zero

/-- The increment split need only hold almost surely under the actual
kernel product, as it does when the continuation's initial state matches. -/
theorem cylinder_identity_of_split (increment test post : Ω × Y → ℝ)
    (pre originalTest : Ω → ℝ)
    (hsplit : increment =ᵐ[μ ⊗ₘ κ] fun z ↦ pre z.1 + post z)
    (hpre : ∀ z : Ω × Y, pre z.1 ≠ 0 → test z = originalTest z.1)
    (hipre : Integrable (fun z : Ω × Y ↦ test z * pre z.1) (μ ⊗ₘ κ))
    (hipost : Integrable (fun z : Ω × Y ↦ test z * post z) (μ ⊗ₘ κ))
    (hpre_zero : (∫ ω, originalTest ω * pre ω ∂μ) = 0)
    (hpost_zero : ∀ᵐ ω ∂μ, (∫ y, test (ω, y) * post (ω, y) ∂κ ω) = 0) :
    (∫ z, test z * increment z ∂(μ ⊗ₘ κ)) = 0 :=
  (integral_congr_ae (hsplit.mono fun z hz ↦ congrArg (fun v ↦ test z * v) hz)).trans
    (cylinder_identity μ κ test post pre originalTest hpre hipre hipost hpre_zero hpost_zero)

end SHEStochastic.KernelMartingalePasting
