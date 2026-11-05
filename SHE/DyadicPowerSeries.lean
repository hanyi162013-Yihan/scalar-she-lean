module

public import SHE.DyadicTransport

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.DyadicPowerSeries
open Finset

def term (A p q : ℝ) (n : ℕ) : ℝ := (min 1 (A/(2:ℝ)^n))^q*((2:ℝ)^n)^p
def constant (p q : ℝ) : ℝ := ((2:ℝ)^p-1)⁻¹+(2:ℝ)^q*(1-(2:ℝ)^(p-q))⁻¹

theorem term_nonneg {A : ℝ} (hA : 0 ≤ A) (p q : ℝ) (n : ℕ) : 0 ≤ term A p q n := by
  unfold term
  exact mul_nonneg (Real.rpow_nonneg (le_min (by norm_num) (by positivity)) _)
    (Real.rpow_nonneg (by positivity) _)

theorem constant_pos {p q : ℝ} (hp : 0 < p) (hpq : p < q) : 0 < constant p q := by
  have hP : 1 < (2:ℝ)^p := by simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hp
  have hR : (2:ℝ)^(p-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hpq)
  unfold constant
  exact add_pos (inv_pos.mpr (sub_pos.mpr hP)) (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (inv_pos.mpr (sub_pos.mpr hR)))

theorem coarse_bound {A p q : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (n : ℕ) :
    term A p q n ≤ ((2:ℝ)^p)^n := by
  have hmin : 0 ≤ min 1 (A/(2:ℝ)^n) := le_min (by norm_num) (by positivity)
  have hh : (min 1 (A/(2:ℝ)^n))^q ≤ 1 := by
    calc
      _ ≤ (1:ℝ)^q := Real.rpow_le_rpow hmin (min_le_left _ _) hq
      _ = 1 := Real.one_rpow _
  simpa only [term,one_mul,Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)] using
    mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 2^n) p)

theorem tail_bound {A p q : ℝ} {N : ℕ} (hA : 0 ≤ A) (hcut : A ≤ 2*(2:ℝ)^N)
    (hq : 0 ≤ q) (n : ℕ) :
    term A p q (n+N) ≤ (2:ℝ)^q*((2:ℝ)^N)^p*((2:ℝ)^(p-q))^n := by
  have hr : A/(2:ℝ)^(n+N) ≤ 2/(2:ℝ)^n := by
    rw [pow_add]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^n*2^N)).mpr
    convert hcut using 1
    field_simp
  have hmin : 0 ≤ min 1 (A/(2:ℝ)^(n+N)) := le_min (by norm_num) (by positivity)
  have hh : (min 1 (A/(2:ℝ)^(n+N)))^q ≤ (2/(2:ℝ)^n)^q :=
    Real.rpow_le_rpow hmin ((min_le_right _ _).trans hr) hq
  apply (mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 2^(n+N)) p)).trans_eq
  rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),pow_add,
    Real.mul_rpow (by positivity) (by positivity),
    Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2) (p-q) n,
    Real.rpow_sub (by positivity : (0:ℝ) < 2^n)]
  ring

theorem series {A p q : ℝ} (hA : 1 ≤ A) (hp : 0 < p) (hpq : p < q) :
    Summable (term A p q) ∧ (∑' n,term A p q n) ≤ constant p q*A^p := by
  have hA0 : 0 ≤ A := (by norm_num : (0:ℝ) ≤ 1).trans hA
  have hq : 0 < q := hp.trans hpq
  obtain ⟨N,hNA,hAN⟩ := exists_nat_pow_near hA (by norm_num : (1:ℝ) < 2)
  have hcut : A ≤ 2*(2:ℝ)^N := by rw [pow_succ] at hAN; linarith
  have hR0 : 0 ≤ (2:ℝ)^(p-q) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hR1 : (2:ℝ)^(p-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hpq)
  have hP1 : 1 < (2:ℝ)^p := by simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hp
  have htail := (summable_geometric_of_lt_one hR0 hR1).mul_left ((2:ℝ)^q*((2:ℝ)^N)^p)
  have hsTail : Summable (fun n => term A p q (n+N)) :=
    Summable.of_nonneg_of_le (fun n => term_nonneg hA0 p q _) (tail_bound hA0 hcut hq.le) htail
  have hs := (summable_nat_add_iff N).mp hsTail
  refine ⟨hs,?_⟩
  have hc : (∑ n ∈ range N,term A p q n) ≤ ((2:ℝ)^N)^p/((2:ℝ)^p-1) := by
    calc
      _ ≤ ∑ n ∈ range N,((2:ℝ)^p)^n := Finset.sum_le_sum (fun n _ => coarse_bound hA0 hq.le n)
      _ = (((2:ℝ)^p)^N-1)/((2:ℝ)^p-1) := geom_sum_eq hP1.ne' _
      _ ≤ ((2:ℝ)^N)^p/((2:ℝ)^p-1) := by
        rw [← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)]
        exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hP1.le)
  have ht : (∑' n,term A p q (n+N)) ≤
      (2:ℝ)^q*((2:ℝ)^N)^p/(1-(2:ℝ)^(p-q)) := by
    calc
      _ ≤ ∑' n,(2:ℝ)^q*((2:ℝ)^N)^p*((2:ℝ)^(p-q))^n :=
        hsTail.tsum_le_tsum (tail_bound hA0 hcut hq.le) htail
      _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hR0 hR1]; ring
  rw [← hs.sum_add_tsum_nat_add N]
  calc
    _ ≤ ((2:ℝ)^N)^p/((2:ℝ)^p-1)+(2:ℝ)^q*((2:ℝ)^N)^p/(1-(2:ℝ)^(p-q)) := add_le_add hc ht
    _ = constant p q*((2:ℝ)^N)^p := by unfold constant; simp only [div_eq_mul_inv]; ring
    _ ≤ constant p q*A^p := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hNA hp.le) (constant_pos hp hpq).le

end SHE.DyadicPowerSeries
