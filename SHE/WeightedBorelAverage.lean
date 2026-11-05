module

public import SHE.FiniteWordScores

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.WeightedBorelAverage
open Set MeasureTheory ProbabilityTheory GaussianIncrement FiniteCenteredProduct
open scoped BigOperators
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

def average (μ : Measure X) (w : X → ℝ) (shift : X → State n) (F : State n → ℝ)
    (z : State n) : ℝ := ∫ x, w x * F (z + shift x) ∂μ

theorem integrable (μ : Measure X) (w : X → ℝ) (hw : Integrable w μ)
    (shift : X → State n) (hs : Measurable shift) (F : State n → ℝ) (hF : Measurable F)
    (B : ℝ) (hb : ∀ z, |F z| ≤ B) (z : State n) :
    Integrable (fun x => w x * F (z + shift x)) μ :=
  hw.mul_bdd (c := B) (hF.comp (measurable_const.add hs)).aestronglyMeasurable
    (ae_of_all _ (fun x => by
      change ‖F (z + shift x)‖ ≤ B
      simpa only [Real.norm_eq_abs] using hb (z + shift x)))

theorem measurable (μ : Measure X) [SFinite μ] (w : X → ℝ) (hw : Measurable w)
    (shift : X → State n) (hs : Measurable shift) (F : State n → ℝ) (hF : Measurable F) :
    Measurable (average μ w shift F) := by
  have h : Measurable (fun p : State n × X => w p.2 * F (p.1 + shift p.2)) :=
    (hw.comp measurable_snd).mul (hF.comp (measurable_fst.add (hs.comp measurable_snd)))
  exact h.stronglyMeasurable.integral_prod_right' |>.measurable

theorem bound (μ : Measure X) (w : X → ℝ) (hw : Integrable w μ)
    (shift : X → State n) (hs : Measurable shift) (F : State n → ℝ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, |F z| ≤ B) (z : State n) :
    |average μ w shift F z| ≤ B * ∫ x, |w x| ∂μ := by
  have hi := integrable μ w hw shift hs F hF B hb z
  calc
    _ ≤ ∫ x, |w x * F (z + shift x)| ∂μ := by
      simpa only [average, Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => w x * F (z + shift x))
    _ ≤ ∫ x, B * |w x| ∂μ := by
      apply integral_mono hi.norm (hw.norm.const_mul B)
      intro x
      change |w x * F (z + shift x)| ≤ B * |w x|
      rw [abs_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb (z + shift x)) (abs_nonneg (w x))
    _ = _ := integral_const_mul _ _

theorem const_mul (μ : Measure X) (w : X → ℝ) (shift : X → State n)
    (F : State n → ℝ) (c : ℝ) (z : State n) :
    average μ w shift (fun y => c * F y) z = c * average μ w shift F z := by
  unfold average
  simp_rw [show ∀ x, w x * (c * F (z + shift x)) = c * (w x * F (z + shift x)) by intro x; ring]
  exact integral_const_mul _ _

theorem neg (μ : Measure X) (w : X → ℝ) (shift : X → State n)
    (F : State n → ℝ) (z : State n) :
    average μ w shift (fun y => -F y) z = -average μ w shift F z := by
  simpa only [neg_one_mul] using const_mul μ w shift F (-1) z

theorem finset_sum {ι : Type*} (s : Finset ι) (μ : Measure X) (w : X → ℝ) (hw : Integrable w μ)
    (shift : X → State n) (hs : Measurable shift) (F : ι → State n → ℝ)
    (hF : ∀ i ∈ s, Measurable (F i)) (B : ι → ℝ) (hb : ∀ i ∈ s, ∀ z, |F i z| ≤ B i) (z : State n) :
    average μ w shift (fun y => ∑ i ∈ s, F i y) z = ∑ i ∈ s, average μ w shift (F i) z := by
  unfold average
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => integrable μ w hw shift hs (F i) (hF i hi) (B i) (hb i hi) z)

theorem test_expansion {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (μ : Measure X) (w : X → ℝ) (hw : Integrable w μ)
    (shift : X → State n) (hs : Measurable shift)
    (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) (z : State n) :
    average μ w shift (test s R a b) z =
      ∑ t ∈ s.powerset, coefficient s t b * average μ w shift (monomial R a t) z := by
  have he : test s R a b = fun y => ∑ t ∈ s.powerset, coefficient s t b * monomial R a t y :=
    funext (FiniteCenteredProduct.expansion s R a b)
  have hm (t : Finset ι) (ht : t ∈ s.powerset) : Measurable (fun y => coefficient s t b * monomial R a t y) :=
    measurable_const.mul (measurable_monomial t R a hR (fun i hi => ha i (Finset.mem_powerset.mp ht hi)))
  have hb (t : Finset ι) (ht : t ∈ s.powerset) (y : State n) :
      |coefficient s t b * monomial R a t y| ≤ |coefficient s t b| * (B * ∏ i ∈ t, M i) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (monomial_bound t R a B M hB (fun i hi => hM i (Finset.mem_powerset.mp ht hi)) hRb
        (fun i hi => hab i (Finset.mem_powerset.mp ht hi)) y) (abs_nonneg _)
  rw [he, finset_sum s.powerset μ w hw shift hs _ hm _ hb]
  simp_rw [const_mul]

end SHE.WeightedBorelAverage
