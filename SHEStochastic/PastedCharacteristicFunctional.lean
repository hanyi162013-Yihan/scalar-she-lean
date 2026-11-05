module

public import SHEStochastic.PastedPastTests
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.PastedCharacteristicFunctional
open MeasureTheory StoppedPathPasting PastedPastTests
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [Module ℝ E]
  (H : ℝ≥0) (ell : E →L[ℝ] ℝ) (c : ℝ)

/-- The bounded-on-finite-horizons Brownian characteristic functional. -/
def value (x : Path H E) (t : Time H) : ℂ :=
  Complex.exp ((ell (x t - x (origin H)) : ℂ) * Complex.I + (c * t.val : ℝ))

@[simp] theorem value_origin (x : Path H E) : value H ell c x (origin H) = 1 := by
  simp [value, origin]

theorem norm_value (x : Path H E) (t : Time H) :
    ‖value H ell c x t‖ = Real.exp (c * t.val) := by
  simp [value, Complex.norm_exp]

theorem norm_value_le (hc : 0 ≤ c) (x : Path H E) (t : Time H) :
    ‖value H ell c x t‖ ≤ Real.exp (c * H) := by
  rw [norm_value]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 hc)

theorem continuous_value : Continuous (fun p : Path H E × Time H ↦ value H ell c p.1 p.2) := by
  unfold value
  fun_prop

theorem weighted_increment_integrable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hc : 0 ≤ c)
    (test : Ω → ℝ) (C : ℝ) (htest : Measurable test) (hbound : ∀ ω, ‖test ω‖ ≤ C)
    (X : Ω → Path H E) (hX : Measurable X)
    (s t : Ω → Time H) (hs : Measurable s) (ht : Measurable t) :
    Integrable (fun ω ↦ test ω •
      (value H ell c (X ω) (t ω) - value H ell c (X ω) (s ω))) μ := by
  let B := Real.exp (c * H)
  have hv := (continuous_value H ell c).measurable
  apply (integrable_const (C * (B + B))).mono'
    ((htest.smul ((hv.comp (hX.prodMk ht)).sub
      (hv.comp (hX.prodMk hs)))).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω ↦ by
    change ‖test ω • (value H ell c (X ω) (t ω) - value H ell c (X ω) (s ω))‖ ≤ C * (B+B)
    rw [norm_smul]
    exact mul_le_mul (hbound ω)
      ((norm_sub_le _ _).trans (add_le_add (norm_value_le H ell c hc (X ω) (t ω))
        (norm_value_le H ell c hc (X ω) (s ω))))
      (norm_nonneg _) ((norm_nonneg _).trans (hbound ω))

theorem ages_add (r t : Time H) :
    (pastTime H r t).val + (futureTime H r t).val = t.val := by
  change min t.val r.val + max (t.val - r.val) 0 = t.val
  by_cases ht : t.val ≤ r.val
  · rw [min_eq_left ht, max_eq_right (sub_nonpos.mpr ht), add_zero]
  · rw [min_eq_right (le_of_not_ge ht), max_eq_left (sub_nonneg.mpr (le_of_not_ge ht))]
    ring

/-- Driver increments concatenate multiplicatively, even when the two
paths do not have matching initial values. -/
theorem value_paste (r t : Time H) (x y : Path H E) :
    value H ell c (paste H r x y) t =
      value H ell c x (pastTime H r t) * value H ell c y (futureTime H r t) := by
  have hzero : paste H r x y (origin H) = x (origin H) :=
    paste_before H r (origin H) x y r.property.1
  simp only [value]
  rw [hzero, paste_apply, ← Complex.exp_add]
  apply congrArg Complex.exp
  have he : x (pastTime H r t) + y (futureTime H r t) - y (origin H) - x (origin H) =
      (x (pastTime H r t) - x (origin H)) +
        (y (futureTime H r t) - y (origin H)) := by abel
  rw [he, map_add, Complex.ofReal_add]
  have ha := ages_add H r t
  push_cast
  have hcast : (t.val : ℂ) = ((pastTime H r t).val : ℂ) + ((futureTime H r t).val : ℂ) :=
    by exact_mod_cast ha.symm
  rw [hcast]
  ring

private theorem correction_at_join (r t : Time H) (x y : Path H E) :
    value H ell c x (pastTime H r t) * (value H ell c y (futureTime H r t) - 1) =
      value H ell c x r * (value H ell c y (futureTime H r t) - 1) := by
  by_cases ht : t.val ≤ r.val
  · have hf : futureTime H r t = origin H :=
      Subtype.ext (max_eq_right (sub_nonpos.mpr ht))
    rw [hf, value_origin, sub_self, mul_zero, mul_zero]
  · have hp : pastTime H r t = r := Subtype.ext (min_eq_right (le_of_not_ge ht))
    rw [hp]

/-- The characteristic increment has an original stopped part and a
future part multiplied by its value at the join. -/
theorem increment_paste (r s t : Time H) (x y : Path H E) :
    value H ell c (paste H r x y) t - value H ell c (paste H r x y) s =
      (value H ell c x (pastTime H r t) - value H ell c x (pastTime H r s)) +
        value H ell c x r *
          (value H ell c y (futureTime H r t) - value H ell c y (futureTime H r s)) := by
  rw [value_paste, value_paste]
  have ht := correction_at_join H ell c r t x y
  have hs := correction_at_join H ell c r s x y
  linear_combination ht - hs

theorem test_of_pre_nonzero (s t r : Time H) (hst : s.val ≤ t.val)
    (test : Path H E → ℝ) (htest : UsesPast H s test) (x y : Path H E)
    (hne : value H ell c x (pastTime H r t) - value H ell c x (pastTime H r s) ≠ 0) :
    test (paste H r x y) = test x := by
  apply test_before H s r test htest x y
  apply le_of_not_gt
  intro hrs
  have hs : pastTime H r s = r := Subtype.ext (min_eq_right hrs.le)
  have ht : pastTime H r t = r := Subtype.ext (min_eq_right (hrs.le.trans hst))
  exact hne (by rw [hs, ht, sub_self])

end SHEStochastic.PastedCharacteristicFunctional
