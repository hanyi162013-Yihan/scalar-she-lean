module

public import SHE.HaarOperator
public import SHE.HeatTrace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat
local instance haarSingleHeat_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem heatWeight_square_le {t : ℝ} (ht : 0 < t) (n : ℤ) :
    ‖heatWeight t n‖ ^ 2 ≤ HeatTrace.multiplier 1 0 t n := by
  rw [heatWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    max_eq_left ht.le, pow_two, ← Real.exp_add]
  simp only [HeatTrace.multiplier, neg_zero, Real.rpow_zero, one_mul]
  apply Real.exp_le_exp.mpr
  have hs : (1 : ℝ) ≤ 2 * (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
  have hp := mul_nonneg (mul_nonneg ht.le (sq_nonneg (n : ℝ))) (sub_nonneg.mpr hs)
  nlinarith

theorem heatWeight_square_summable {t : ℝ} (ht : 0 < t) : Summable (fun n : ℤ => ‖heatWeight t n‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (heatWeight_square_le ht)
    (HeatTrace.multiplier_int_summable (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 0) ht)

theorem heatWeight_trace_bound {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, ‖heatWeight t n‖ ^ 2) ≤
      1 + 2 * HeatTrace.fractionalGaussianIntegral 0 * t ^ (-(1 / 2 : ℝ)) := by
  have hh := (heatWeight_square_summable ht).tsum_le_tsum (heatWeight_square_le ht)
    (HeatTrace.multiplier_int_summable (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 0) ht)
  have he := HeatTrace.centered_heat_trace_bound
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1/2) ht
  exact hh.trans (by simpa only [zero_sub] using he)

/-- The true single weighted-Haar factor is Hilbert--Schmidt after
positive heat time. Its bound uses only the covariance upper bound `U`.
Both countable summation orders are justified by absolute convergence. -/
theorem global_single_heat_trace {t : ℝ} (ht : 0 < t)
    (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    Summable (fun q : HaarNode => ‖heat t (globalHaarColumn q f)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (globalHaarColumn q f)‖ ^ 2) ≤
        U * ∑' n : ℤ, ‖heatWeight t n‖ ^ 2 := by
  let F : ℤ × HaarNode → ℝ := fun nq => ‖heatWeight t nq.1‖ ^ 2 *
    ‖fourierCoeff (globalHaarColumn nq.2 f) nq.1‖ ^ 2
  have hcoeff (n : ℤ) : Summable (fun q : HaarNode => ‖fourierCoeff (globalHaarColumn q f) n‖ ^ 2) ∧
      (∑' q : HaarNode, ‖fourierCoeff (globalHaarColumn q f) n‖ ^ 2) ≤ U := by
    have hb := globalHaarColumn_bessel f m U hm hfreal hfbound (fourierBasis n)
    have he (q : HaarNode) : ‖fourierCoeff (globalHaarColumn q f) n‖ ^ 2 =
        ‖inner ℂ (globalHaarColumn q f) (fourierBasis n)‖ ^ 2 := by
      rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply, norm_inner_symm]
    simp only [he] at *
    simpa only [fourierBasis.orthonormal.norm_eq_one, one_pow, mul_one] using hb
  have hrow (n : ℤ) : Summable (fun q : HaarNode => F (n,q)) := by
    dsimp only [F]
    exact (hcoeff n).1.mul_left _
  have hrowsum (n : ℤ) : (∑' q : HaarNode, F (n,q)) ≤ ‖heatWeight t n‖ ^ 2 * U := by
    dsimp only [F]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hcoeff n).2 (sq_nonneg _)
  have houter : Summable (fun n : ℤ => ∑' q : HaarNode, F (n,q)) :=
    Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      hrowsum ((heatWeight_square_summable ht).mul_right U)
  have hprod : Summable F := (summable_prod_of_nonneg
    (fun nq => mul_nonneg (sq_nonneg _) (sq_nonneg _))).mpr ⟨hrow, houter⟩
  have hcol (q : HaarNode) : (∑' n : ℤ, F (n,q)) = ‖heat t (globalHaarColumn q f)‖ ^ 2 := by
    rw [norm_sq_fourier]
    apply tsum_congr
    intro n
    simp only [F, heat_fourierCoeff, norm_mul, mul_pow]
  have hs : Summable (fun q : HaarNode => ‖heat t (globalHaarColumn q f)‖ ^ 2) := by
    have hh := hprod.prod_symm.prod
    change Summable (fun q : HaarNode => ∑' n : ℤ, F (n,q)) at hh
    simpa only [hcol] using hh
  refine ⟨hs, ?_⟩
  calc
    _ = ∑' q : HaarNode, ∑' n : ℤ, F (n,q) := by simp only [hcol]
    _ = ∑' nq : ℤ × HaarNode, F nq := by
      have he := hprod.prod_symm.tsum_prod.symm
      change (∑' q : HaarNode, ∑' n : ℤ, F (n,q)) = ∑' qn : HaarNode × ℤ, F (qn.2,qn.1) at he
      exact he.trans ((Equiv.prodComm HaarNode ℤ).tsum_eq F)
    _ = ∑' n : ℤ, ∑' q : HaarNode, F (n,q) := hprod.tsum_prod
    _ ≤ ∑' n : ℤ, ‖heatWeight t n‖ ^ 2 * U := houter.tsum_le_tsum hrowsum ((heatWeight_square_summable ht).mul_right U)
    _ = _ := by rw [tsum_mul_right, mul_comm]

theorem global_single_heat {t : ℝ} (ht : 0 < t)
    (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    Summable (fun q : HaarNode => ‖heat t (globalHaarColumn q f)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (globalHaarColumn q f)‖ ^ 2) ≤
        U * (1 + 2 * HeatTrace.fractionalGaussianIntegral 0 * t ^ (-(1 / 2 : ℝ))) := by
  have hh := global_single_heat_trace ht f m U hm hfreal hfbound
  exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_left (heatWeight_trace_bound ht)
    (elliptic_upper_nonneg f m U hm hfbound))⟩

end SHE.FiniteHaar
