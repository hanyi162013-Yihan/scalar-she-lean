module

public import SHEStochastic.StoppedPathPasting
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.PastedGeneratorFunctional
open MeasureTheory Set StoppedPathPasting
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] (H : ℝ≥0)

/-- A path extended constantly outside its time interval, solely for
writing ordinary real interval integrals. -/
def read (x : Path H E) (s : ℝ) : E := x (Set.projIcc (0 : ℝ) (H : ℝ) H.property s)

theorem continuous_read (x : Path H E) : Continuous (read H x) :=
  x.continuous.comp continuous_projIcc

@[simp] theorem read_val (x : Path H E) (t : Time H) : read H x t.val = x t := by
  simp only [read, Set.projIcc_val]

theorem read_before (r : Time H) (x y : Path H E) (s : ℝ)
    (hs : s ∈ Icc 0 r.val) : read H (paste H r x y) s = read H x s := by
  have hsH : s ∈ Icc (0 : ℝ) H := ⟨hs.1, hs.2.trans r.property.2⟩
  change read H (paste H r x y) (⟨s, hsH⟩ : Time H).val =
    read H x (⟨s, hsH⟩ : Time H).val
  rw [read_val, read_val]
  exact paste_before H r ⟨s, hsH⟩ x y hs.2

theorem read_after (r : Time H) (x y : Path H E)
    (hjoin : y (origin H) = x r) (s : ℝ) (hs : s ∈ Icc r.val H) :
    read H (paste H r x y) s = read H y (s - r.val) := by
  have hsH : s ∈ Icc (0 : ℝ) H := ⟨r.property.1.trans hs.1, hs.2⟩
  have hshift : s - r.val ∈ Icc (0 : ℝ) H :=
    ⟨sub_nonneg.mpr hs.1, (sub_le_self _ r.property.1).trans hs.2⟩
  change read H (paste H r x y) (⟨s, hsH⟩ : Time H).val =
    read H y (⟨s - r.val, hshift⟩ : Time H).val
  rw [read_val, read_val]
  rw [paste_after H r ⟨s, hsH⟩ x y hs.1 hjoin]
  congr 1
  apply Subtype.ext
  exact max_eq_left hshift.1

theorem integral_before (b : E → ℝ) (r t : Time H) (x y : Path H E)
    (ht : t.val ≤ r.val) :
    (∫ s in 0..t.val, b (read H (paste H r x y) s)) =
      ∫ s in 0..t.val, b (read H x s) := by
  apply intervalIntegral.integral_congr_Ioo_of_le t.property.1
  intro s hs
  change b (read H (paste H r x y) s) = b (read H x s)
  rw [read_before H r x y s ⟨hs.1.le, hs.2.le.trans ht⟩]

theorem integral_after (b : E → ℝ) (r t : Time H) (x y : Path H E)
    (ht : r.val ≤ t.val) (hjoin : y (origin H) = x r) :
    (∫ s in r.val..t.val, b (read H (paste H r x y) s)) =
      ∫ s in 0..(t.val - r.val), b (read H y s) := by
  calc
    _ = ∫ s in r.val..t.val, b (read H y (s - r.val)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht
      intro s hs
      change b (read H (paste H r x y) s) = b (read H y (s - r.val))
      rw [read_after H r x y hjoin s ⟨hs.1.le, hs.2.le.trans t.property.2⟩]
    _ = _ := by
      simpa only [sub_self] using
        (intervalIntegral.integral_comp_sub_right (fun s ↦ b (read H y s))
          (a := r.val) (b := t.val) r.val)

/-- The canonical cylinder-test martingale expression. Its drift b is
the generator applied to the cylinder test f; no stochastic assertion
is built into this deterministic definition. -/
def value (f b : E → ℝ) (x : Path H E) (t : Time H) : ℝ :=
  f (x t) - f (x (origin H)) - ∫ s in 0..t.val, b (read H x s)

theorem continuous_value (f b : E → ℝ) (hf : Continuous f) (hb : Continuous b) :
    Continuous (fun p : Path H E × Time H ↦ value H f b p.1 p.2) := by
  have hi : Continuous (fun p : Path H E × Time H ↦
      ∫ s in 0..p.2.val, b (read H p.1 s)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume)
    · exact hb.comp (continuous_eval.comp (continuous_fst.fst.prodMk
        ((continuous_projIcc (h := H.property)).comp continuous_snd)))
    · exact continuous_subtype_val.comp continuous_snd
  exact ((hf.comp continuous_eval).sub
    (hf.comp ((continuous_eval_const (origin H)).comp continuous_fst))).sub hi

/-- Bounded cylinder tests and bounded generator values give a uniform
bound on the entire martingale expression, including random times. -/
theorem norm_value_bound (f b : BoundedContinuousFunction E ℝ)
    (x : Path H E) (t : Time H) :
    ‖value H f b x t‖ ≤ 2 * ‖f‖ + ‖b‖ * H := by
  have hi : ‖∫ s in 0..t.val, b (read H x s)‖ ≤ ‖b‖ * H := by
    calc
      _ ≤ ‖b‖ * |t.val - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ ↦ b.norm_coe_le_norm _)
      _ ≤ ‖b‖ * H := by
        rw [sub_zero, abs_of_nonneg t.property.1]
        exact mul_le_mul_of_nonneg_left t.property.2 (norm_nonneg b)
  calc
    _ ≤ ‖f (x t) - f (x (origin H))‖ + ‖∫ s in 0..t.val, b (read H x s)‖ := norm_sub_le _ _
    _ ≤ (‖f‖ + ‖f‖) + ‖b‖ * H :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _))) hi
    _ = _ := by ring

/-- All weighted random-time increments used in the pasting proof are
integrable under finite measures. This follows from the uniform bound,
not from a separate moment assumption on the continuation. -/
theorem weighted_increment_integrable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f b : BoundedContinuousFunction E ℝ) (test : Ω → ℝ) (C : ℝ)
    (htest : Measurable test) (hbound : ∀ ω, ‖test ω‖ ≤ C)
    (X : Ω → Path H E) (hX : Measurable X)
    (s t : Ω → Time H) (hs : Measurable s) (ht : Measurable t) :
    Integrable (fun ω ↦ test ω * (value H f b (X ω) (t ω) - value H f b (X ω) (s ω))) μ := by
  let B : ℝ := 2 * ‖f‖ + ‖b‖ * H
  have hv := (continuous_value H f b f.continuous b.continuous).measurable
  apply (integrable_const (C * (B + B))).mono'
    ((htest.mul ((hv.comp (hX.prodMk ht)).sub
      (hv.comp (hX.prodMk hs)))).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω ↦ by
    change ‖test ω * (value H f b (X ω) (t ω) - value H f b (X ω) (s ω))‖ ≤ C * (B + B)
    rw [norm_mul]
    exact mul_le_mul (hbound ω)
      ((norm_sub_le _ _).trans (add_le_add (norm_value_bound H f b (X ω) (t ω))
        (norm_value_bound H f b (X ω) (s ω))))
      (norm_nonneg _) ((norm_nonneg _).trans (hbound ω))

@[simp] theorem value_origin (f b : E → ℝ) (x : Path H E) :
    value H f b x (origin H) = 0 := by simp [value, origin]

/-- Generator values need agree only strictly before the exit to give
the SAME stopped martingale expression. The endpoint has zero time
measure, so no equality of the two coefficients after exit is assumed. -/
theorem value_congr_before (f b c : E → ℝ) (r t : Time H) (x : Path H E)
    (hbc : ∀ s : Time H, s.val < r.val → b (x s) = c (x s)) :
    value H f b x (pastTime H r t) = value H f c x (pastTime H r t) := by
  have hi : (∫ s in 0..(pastTime H r t).val, b (read H x s)) =
      ∫ s in 0..(pastTime H r t).val, c (read H x s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (pastTime H r t).property.1
    intro s hs
    have hsH : s ∈ Set.Icc (0 : ℝ) H :=
      ⟨hs.1.le, hs.2.le.trans (pastTime H r t).property.2⟩
    change b (read H x (⟨s, hsH⟩ : Time H).val) = c (read H x (⟨s, hsH⟩ : Time H).val)
    rw [read_val]
    exact hbc ⟨s, hsH⟩ (hs.2.trans_le (min_le_right _ _))
  simp only [value, hi]

theorem value_before (f b : E → ℝ) (r t : Time H) (x y : Path H E)
    (ht : t.val ≤ r.val) : value H f b (paste H r x y) t = value H f b x t := by
  simp only [value, paste_before H r t x y ht,
    paste_before H r (origin H) x y r.property.1,
    integral_before H b r t x y ht]

theorem value_after (f b : E → ℝ) (hb : Continuous b)
    (r t : Time H) (x y : Path H E) (ht : r.val ≤ t.val)
    (hjoin : y (origin H) = x r) :
    value H f b (paste H r x y) t =
      value H f b x r + value H f b y (futureTime H r t) := by
  have hi (u v : ℝ) : IntervalIntegrable (fun s ↦ b (read H (paste H r x y) s)) volume u v :=
    (hb.comp (continuous_read H (paste H r x y))).intervalIntegrable u v
  have he : (∫ s in 0..t.val, b (read H (paste H r x y) s)) =
      (∫ s in 0..r.val, b (read H x s)) +
        ∫ s in 0..(t.val - r.val), b (read H y s) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 r.val) (hi r.val t.val)]
    rw [integral_before H b r r x y le_rfl, integral_after H b r t x y ht hjoin]
  have hf : (futureTime H r t).val = t.val - r.val := max_eq_left (sub_nonneg.mpr ht)
  simp only [value, paste_after H r t x y ht hjoin,
    paste_before H r (origin H) x y r.property.1, he, hf, hjoin]
  ring

/-- Splitting a canonical generator martingale at the join requires
only the matching initial state and continuity of its scalar drift. -/
theorem value_paste (f b : E → ℝ) (hb : Continuous b)
    (r t : Time H) (x y : Path H E) (hjoin : y (origin H) = x r) :
    value H f b (paste H r x y) t =
      value H f b x (pastTime H r t) + value H f b y (futureTime H r t) := by
  rcases le_total t.val r.val with ht | ht
  · have hp : pastTime H r t = t := Subtype.ext (min_eq_left ht)
    have hf : futureTime H r t = origin H := Subtype.ext (max_eq_right (sub_nonpos.mpr ht))
    rw [hp, hf, value_origin, add_zero]
    exact value_before H f b r t x y ht
  · have hp : pastTime H r t = r := Subtype.ext (min_eq_right ht)
    rw [hp]
    exact value_after H f b hb r t x y ht hjoin

theorem increment_paste (f b : E → ℝ) (hb : Continuous b)
    (r s t : Time H) (x y : Path H E) (hjoin : y (origin H) = x r) :
    value H f b (paste H r x y) t - value H f b (paste H r x y) s =
      (value H f b x (pastTime H r t) - value H f b x (pastTime H r s)) +
      (value H f b y (futureTime H r t) - value H f b y (futureTime H r s)) := by
  rw [value_paste H f b hb r t x y hjoin, value_paste H f b hb r s x y hjoin]
  ring

end SHEStochastic.PastedGeneratorFunctional
