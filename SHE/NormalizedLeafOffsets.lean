module

public import SHE.GaussianKernelShiftedLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.NormalizedLeafOffsets
open Set MeasureTheory Real
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- The scalar current offsets are normalized at their ORIGINAL full
native ages. The budget is linear in their actual higher moments. -/
def budget (age offset : Fin m→ℝ) (p degree : ℝ) : ℝ :=
  ∑ j,|offset j|^p/(age j)^degree

theorem budget_nonneg (age offset : Fin m→ℝ) (p degree : ℝ) (hage : ∀ j,0<age j) :
    0≤budget age offset p degree :=
  Finset.sum_nonneg (fun j _=>div_nonneg (rpow_nonneg (abs_nonneg _) _) (rpow_nonneg (hage j).le _))

theorem offset_le_budget (age offset : Fin m→ℝ) (p degree : ℝ) (hage : ∀ j,0<age j) (j : Fin m) :
    |offset j|^p≤budget age offset p degree*(age j)^degree := by
  have hs : |offset j|^p/(age j)^degree≤budget age offset p degree :=
    Finset.single_le_sum (fun i _=>div_nonneg (rpow_nonneg (abs_nonneg _) _)
      (rpow_nonneg (hage i).le _)) (Finset.mem_univ j)
  have hh := mul_le_mul_of_nonneg_right hs (rpow_nonneg (hage j).le degree)
  simpa only [div_mul_cancel₀ _ (rpow_pos_of_pos (hage j) degree).ne'] using hh

theorem budget_measurable (age : Fin m→ℝ) (offset : Ω→Fin m→ℝ) (hoffset : Measurable offset)
    (p degree : ℝ) : Measurable (fun ω=>budget age (offset ω) p degree) := by
  apply Finset.measurable_sum
  intro j _
  exact ((continuous_abs.measurable.comp ((measurable_pi_apply j).comp hoffset)).pow_const p).div_const _

theorem budget_integrable (μ : Measure Ω) (age : Fin m→ℝ) (offset : Ω→Fin m→ℝ) (p degree : ℝ)
    (hi : ∀ j,Integrable (fun ω=>|offset ω j|^p) μ) :
    Integrable (fun ω=>budget age (offset ω) p degree) μ :=
  integrable_finsetSum Finset.univ (fun j _=>(hi j).div_const _)

/-- The normalized budget is controlled on any finite event measure,
with its EXACT event mass. This is the deterministic integration step
needed for conditional past-event moments and varying Gaussian laws. -/
theorem integral_budget_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (age : Fin m→ℝ) (hage : ∀ j,0<age j) (offset : Ω→Fin m→ℝ) (p degree C : ℝ)
    (hi : ∀ j,Integrable (fun ω=>|offset ω j|^p) μ)
    (hb : ∀ j,(∫ ω,|offset ω j|^p ∂μ)≤C*(age j)^degree*μ.real Set.univ) :
    (∫ ω,budget age (offset ω) p degree ∂μ)≤(m:ℝ)*C*μ.real Set.univ := by
  unfold budget
  rw [integral_finsetSum _ (fun j _=>(hi j).div_const _)]
  have hh : (∑ j : Fin m,∫ ω,|offset ω j|^p/(age j)^degree ∂μ)≤
      ∑ _ : Fin m,C*μ.real Set.univ := by
    apply Finset.sum_le_sum
    intro j _
    rw [integral_div]
    apply (div_le_iff₀ (rpow_pos_of_pos (hage j) degree)).mpr
    convert! hb j using 1
    ring
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh

end SHE.NormalizedLeafOffsets
