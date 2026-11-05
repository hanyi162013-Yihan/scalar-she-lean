module

public import SHEStochastic.LinearHeatMaximum
public import SHEStochastic.SubGaussianFourthMoment
public import SHEStochastic.QuadraticMomentBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.LinearHeatMaximumMoments
open MeasureTheory ProbabilityTheory StoppedPathPasting AdaptedCanonicalPathTests
open PastedLinearHeatFunctional
open scoped NNReal ENNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [Module ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (H : ℝ≥0) (ell : E →L[ℝ] ℝ) (lam : ℝ)
  {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : Ω → Path H E)


def fourthConstant (c : ℝ≥0) : ℝ≥0∞ := 4*ENNReal.ofReal (48*Real.exp (1/2 : ℝ)*(c : ℝ)^2)

theorem fourthConstant_lt_top (c : ℝ≥0) : fourthConstant c < ⊤ :=
  ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

/-- Doob's path maximum and the proved sub-Gaussian fourth moment
supply one bound uniform over all conditional continuation laws. -/
theorem fourth_bound
    (hM : Martingale (fun q x ↦ value H ell lam (X x) (clock H q)) F ν)
    (hMom : ∀ q, MemLp (fun x ↦ value H ell lam (X x) (clock H q)) 4 ν)
    (c : ℝ≥0) (hs : HasSubgaussianMGF (fun x ↦ value H ell lam (X x) (clock H H)) c ν) :
    (∫⁻ x, ENNReal.ofReal ((envelope H ell lam (X x))^4) ∂ν) ≤ fourthConstant c := by
  let M := fun x ↦ value H ell lam (X x) (clock H H)
  have hi : Integrable (fun x ↦ M x^4) ν :=
    QuadraticMomentBounds.fourth_integrable ν (by simpa using hs.memLp (4 : ℝ≥0))
  have hL : (∫⁻ x, ENNReal.ofReal (M x^4) ∂ν) ≤
      ENNReal.ofReal (48*Real.exp (1/2 : ℝ)*(c : ℝ)^2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x ↦ by positivity)]
    exact ENNReal.ofReal_le_ofReal (SubGaussianFourthMoment.integral_fourth_le hs)
  exact (LinearHeatMaximum.fourth_bound H ell lam ν F X hM hMom).trans (mul_le_mul_right hL 4)

/-- The maximum is the fixed Borel norm of the continuous trajectory,
so its finite fourth moment gives an actual L4 observable. -/
theorem envelope_memLp (hX : Measurable X)
    (hM : Martingale (fun q x ↦ value H ell lam (X x) (clock H q)) F ν)
    (hMom : ∀ q, MemLp (fun x ↦ value H ell lam (X x) (clock H q)) 4 ν)
    (c : ℝ≥0) (hs : HasSubgaussianMGF (fun x ↦ value H ell lam (X x) (clock H H)) c ν) :
    MemLp (fun x ↦ envelope H ell lam (X x)) 4 ν := by
  have hm : AEStronglyMeasurable (fun x ↦ envelope H ell lam (X x)) ν :=
    ((continuous_envelope H ell lam).measurable.comp hX).aestronglyMeasurable
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) hm).mpr
  have he (x : Ω) : ‖envelope H ell lam (X x)‖ₑ ^ (4 : ℝ≥0∞).toReal =
      ENNReal.ofReal ((envelope H ell lam (X x))^4) := by
    change ‖envelope H ell lam (X x)‖ₑ ^ ((4 : ℕ) : ℝ) = _
    rw [ENNReal.rpow_natCast, ← ofReal_norm,
      Real.norm_of_nonneg (show 0 ≤ envelope H ell lam (X x) from norm_nonneg _),
      ← ENNReal.ofReal_pow (show 0 ≤ envelope H ell lam (X x) from norm_nonneg _)]
  simp_rw [he]
  exact (fourth_bound H ell lam ν F X hM hMom c hs).trans_lt (fourthConstant_lt_top c)

end SHEStochastic.LinearHeatMaximumMoments
