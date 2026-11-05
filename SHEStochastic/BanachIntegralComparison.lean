module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.HahnBanach

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.BanachIntegralComparison
open MeasureTheory
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Scalar integral comparisons transfer to a Banach norm with no loss
in their constant by applying a norming real linear functional. -/
theorem bound {μ : Measure X} {ν : Measure Y} {f : X → E} {g : Y → E}
    (hf : Integrable f μ) (hg : Integrable g ν) (B : ℝ)
    (h : ∀ L : E →L[ℝ] ℝ, ‖L‖ ≤ 1 →
      |(∫ x, L (f x) ∂μ)-(∫ y, L (g y) ∂ν)| ≤ B) :
    ‖(∫ x, f x ∂μ)-(∫ y, g y ∂ν)‖ ≤ B := by
  let v := (∫ x, f x ∂μ)-(∫ y, g y ∂ν)
  obtain ⟨L,hL,hLv⟩ := exists_dual_vector'' ℝ v
  have hv : L v = ‖v‖ := by simpa only [RCLike.ofReal_real_eq_id,id_eq] using hLv
  have he := h L hL
  rw [L.integral_comp_comm hf,L.integral_comp_comm hg,← map_sub,hv,
    abs_of_nonneg (norm_nonneg v)] at he
  exact he

end SHEStochastic.BanachIntegralComparison
