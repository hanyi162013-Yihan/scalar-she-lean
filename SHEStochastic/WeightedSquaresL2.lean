module

public import SHEStochastic.L2EnergyContinuity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.WeightedSquaresL2
open MeasureTheory
open scoped ENNReal

variable {κ Ω : Type*} [Fintype κ] [MeasurableSpace Ω] {μ : Measure Ω}

def value (w : κ → ℝ) (x : EuclideanSpace ℝ κ) : ℝ := ∑ i, w i * (x i) ^ 2

/-- The weighted quadratic form is locally Lipschitz, uniformly over all
coordinate weights bounded by B. The estimate is dimension independent. -/
theorem pointwise (w : κ → ℝ) (x y : EuclideanSpace ℝ κ)
    (B : ℝ) (hB : 0 ≤ B) (hw : ∀ i, |w i| ≤ B) :
    |value w x - value w y| ≤ B * (‖x - y‖ * ‖x + y‖) := by
  classical
  have hid : value w x - value w y = ∑ i, w i * ((x i - y i) * (x i + y i)) := by
    simp only [value, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  rw [hid]
  calc
    _ ≤ ∑ i, |w i * ((x i - y i) * (x i + y i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B * (|x i - y i| * |x i + y i|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hw i) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = B * ∑ i, |x i - y i| * |x i + y i| := (Finset.mul_sum _ _ _).symm
    _ ≤ B * (Real.sqrt (∑ i, (x i - y i) ^ 2) * Real.sqrt (∑ i, (x i + y i) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun i ↦ |x i - y i|) (fun i ↦ |x i + y i|)
    _ = _ := by
      change B * (Real.sqrt (∑ i, ((x - y) i) ^ 2) * Real.sqrt (∑ i, ((x + y) i) ^ 2)) = _
      rw [← EuclideanSpace.real_norm_sq_eq (x - y), ← EuclideanSpace.real_norm_sq_eq (x + y),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (norm_nonneg _)]

theorem integrable_value (A : Lp (EuclideanSpace ℝ κ) 2 μ) (w : κ → Ω → ℝ)
    (hw : ∀ i, AEStronglyMeasurable (w i) μ)
    (B : ℝ) (hwb : ∀ i ω, |w i ω| ≤ B) :
    Integrable (fun ω ↦ value (fun i ↦ w i ω) (A ω)) μ := by
  apply integrable_finsetSum
  intro i hi
  exact ((Lp.memLp A).eval_piLp i).integrable_sq.bdd_mul (hw i)
    (Filter.Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hwb i ω)

/-- Weighted square sums are L¹-continuous in the original Hilbert L²
inputs, even when the weights are random and differ from cell to cell. -/
theorem integral_sub_le (A D : Lp (EuclideanSpace ℝ κ) 2 μ)
    (w : κ → Ω → ℝ) (hw : ∀ i, AEStronglyMeasurable (w i) μ)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ i ω, |w i ω| ≤ B) :
    (∫ ω, |value (fun i ↦ w i ω) (A ω) - value (fun i ↦ w i ω) (D ω)| ∂μ) ≤
      B * (‖A - D‖ * (‖A‖ + ‖D‖)) := by
  have hi := (Lp.memLp (A - D)).norm.integrable_mul (Lp.memLp (A + D)).norm
  have hC := integral_mul_norm_le_Lp_mul_Lq (f := fun ω ↦ (A - D) ω)
    (g := fun ω ↦ (A + D) ω) Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using Lp.memLp (A - D))
    (by simpa only [ENNReal.ofReal_ofNat] using Lp.memLp (A + D))
  have hr (V : Lp (EuclideanSpace ℝ κ) 2 μ) :
      (∫ ω, ‖V ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖V‖ := by
    rw [show (fun ω ↦ ‖V ω‖ ^ (2 : ℝ)) = (fun ω ↦ ‖V ω‖ ^ (2 : ℕ)) from
      funext fun ω ↦ Real.rpow_two _, ← Real.sqrt_eq_rpow, L2EnergyContinuity.norm_sq,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hr, hr] at hC
  calc
    _ ≤ ∫ ω, B * (‖(A - D) ω‖ * ‖(A + D) ω‖) ∂μ := by
      apply integral_mono_ae ((integrable_value A w hw B hwb).sub
        (integrable_value D w hw B hwb)).abs (hi.const_mul B)
      filter_upwards [Lp.coeFn_sub A D, Lp.coeFn_add A D] with ω hs ha
      change |value (fun i ↦ w i ω) (A ω) - value (fun i ↦ w i ω) (D ω)| ≤
        B * (‖(A - D) ω‖ * ‖(A + D) ω‖)
      rw [hs, ha]
      exact pointwise _ _ _ B hB (fun i ↦ hwb i ω)
    _ = B * ∫ ω, ‖(A - D) ω‖ * ‖(A + D) ω‖ ∂μ := integral_const_mul _ _
    _ ≤ B * (‖A - D‖ * ‖A + D‖) := mul_le_mul_of_nonneg_left hC hB
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_add_le A D) (norm_nonneg _)) hB

end SHEStochastic.WeightedSquaresL2
