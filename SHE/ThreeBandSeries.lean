module

public import SHE.DyadicPowerSeries

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ThreeBandSeries
open Finset

def constant (p q : ℝ) : ℝ := ((2:ℝ)^p-1)⁻¹+(1-(2:ℝ)^(-q))⁻¹+2+(Real.log 2)⁻¹

theorem constant_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 < constant p q := by
  have hP : 1 < (2:ℝ)^p := by simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hp
  have hQ : (2:ℝ)^(-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold constant
  positivity

/-- A literal three-band dyadic series has only logarithmic growth in
the ratio of the two cut scales. The middle-band cardinality is proved
from real logarithms, and the two tails are genuine geometric sums. -/
theorem series {A B p q C : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (hp : 0 < p) (hq : 0 < q)
    (hC : 0 ≤ C) (g : ℕ → ℝ) (hg : ∀ n,0 ≤ g n)
    (hcoarse : ∀ n,(2:ℝ)^n ≤ A → g n ≤ C*((2:ℝ)^n/A)^p)
    (hmiddle : ∀ n,A ≤ (2:ℝ)^n → (2:ℝ)^n ≤ B → g n ≤ C)
    (hfine : ∀ n,B ≤ (2:ℝ)^n → g n ≤ C*(B/(2:ℝ)^n)^q) :
    Summable g ∧ (∑' n,g n) ≤ C*constant p q*(1+Real.log (B/A)) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hB0 : 0 < B := hA0.trans_le hAB
  obtain ⟨N,hNA,hAN⟩ := exists_nat_pow_near hA (by norm_num : (1:ℝ)<2)
  obtain ⟨M,hMB,hBM⟩ := exists_nat_pow_near (hA.trans hAB) (by norm_num : (1:ℝ)<2)
  have hNM : N ≤ M := by
    by_contra hn
    have hh : M+1 ≤ N := by omega
    have hh' : (2:ℝ)^(M+1) ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hh
    linarith
  have hP : 1 < (2:ℝ)^p := by simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hp
  have hQ0 : 0 ≤ (2:ℝ)^(-q) := by positivity
  have hQ1 : (2:ℝ)^(-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have htail_bound (n : ℕ) : g (n+(M+1)) ≤ C*((2:ℝ)^(-q))^n := by
    have hpow : B ≤ (2:ℝ)^(n+(M+1)) := by
      exact hBM.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have hr : B/(2:ℝ)^(n+(M+1)) ≤ ((2:ℝ)^n)⁻¹ := by
      rw [pow_add,inv_eq_one_div]
      apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2^n*2^(M+1)) (by positivity : (0:ℝ)<2^n)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hBM.le (by positivity : (0:ℝ)≤2^n)]
    have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity : 0 ≤ B/(2:ℝ)^(n+(M+1))) hr hq.le) hC
    have he : (((2:ℝ)^n)⁻¹)^q = ((2:ℝ)^(-q))^n := by
      rw [Real.inv_rpow (by positivity : (0:ℝ)≤2^n),← Real.rpow_neg (by positivity : (0:ℝ)≤2^n),
        Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
    exact (hfine _ hpow).trans (by simpa only [he] using hh)
  have hgeom := (summable_geometric_of_lt_one hQ0 hQ1).mul_left C
  have hsTail := Summable.of_nonneg_of_le (fun n => hg (n+(M+1))) htail_bound hgeom
  have hs : Summable g := (summable_nat_add_iff (M+1)).mp hsTail
  have htail : (∑' n,g (n+(M+1))) ≤ C*(1-(2:ℝ)^(-q))⁻¹ := by
    exact (hsTail.tsum_le_tsum htail_bound hgeom).trans_eq (by rw [tsum_mul_left,tsum_geometric_of_lt_one hQ0 hQ1])
  have hprefix : (∑ n ∈ range N,g n) ≤ C*((2:ℝ)^p-1)⁻¹ := by
    have hmajor (n : ℕ) (hn : n ∈ range N) : g n ≤ (C/A^p)*((2:ℝ)^p)^n := by
      have hnA : (2:ℝ)^n ≤ A := (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt (mem_range.mp hn))).trans hNA
      exact (hcoarse n hnA).trans_eq (by
        rw [Real.div_rpow (by positivity : (0:ℝ)≤2^n) hA0.le,Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
        ring)
    have hr : ((2:ℝ)^N)^p/A^p ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hA0 _)).mpr
      (Real.rpow_le_rpow (by positivity) hNA hp.le)
    calc
      _ ≤ ∑ n ∈ range N,(C/A^p)*((2:ℝ)^p)^n := sum_le_sum hmajor
      _ = (C/A^p)*((((2:ℝ)^p)^N-1)/((2:ℝ)^p-1)) := by rw [← mul_sum,geom_sum_eq hP.ne']
      _ ≤ (C/A^p)*((((2:ℝ)^p)^N)/((2:ℝ)^p-1)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hP.le)) (by positivity)
      _ = (C*((2:ℝ)^p-1)⁻¹)*(((2:ℝ)^N)^p/A^p) := by
        rw [← Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
        ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ C*((2:ℝ)^p-1)⁻¹)
  let L := M+1-N
  have hcut : N+L = M+1 := by dsimp [L]; omega
  have hmiddle' : (∑ n ∈ range L,g (n+N)) ≤ (L:ℝ)*C := by
    calc
      _ ≤ ∑ _n ∈ range L,C := by
        apply sum_le_sum
        intro n hn
        have hnM : n+N ≤ M := by have hh := mem_range.mp hn; dsimp only [L] at hh; omega
        have hnB : (2:ℝ)^(n+N) ≤ B := (pow_le_pow_right₀ (by norm_num) hnM).trans hMB
        by_cases hnA : (2:ℝ)^(n+N) ≤ A
        · have hh := Real.rpow_le_one (by positivity : 0 ≤ (2:ℝ)^(n+N)/A) ((div_le_one hA0).mpr hnA) hp.le
          exact (hcoarse _ hnA).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hC)
        · exact hmiddle _ (le_of_not_ge hnA) hnB
      _ = _ := by simp [mul_comm]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogA : Real.log A ≤ ((N:ℝ)+1)*Real.log 2 := by
    have hh := Real.log_le_log hA0 hAN.le
    simpa only [Real.log_pow,Nat.cast_add,Nat.cast_one] using hh
  have hlogB : (M:ℝ)*Real.log 2 ≤ Real.log B := by
    have hh := Real.log_le_log (by positivity : (0:ℝ)<2^M) hMB
    simpa only [Real.log_pow] using hh
  have hL : (L:ℝ) ≤ 2+Real.log (B/A)/Real.log 2 := by
    have he : (L:ℝ) = (M:ℝ)+1-(N:ℝ) := by
      dsimp [L]
      rw [Nat.cast_sub (by omega : N ≤ M+1),Nat.cast_add,Nat.cast_one]
    rw [he,Real.log_div hB0.ne' hA0.ne']
    have hh : ((M:ℝ)+1-(N:ℝ)-2)*Real.log 2 ≤ Real.log B-Real.log A := by
      nlinarith only [hlogA,hlogB]
    have hh' := (le_div_iff₀ hlog2).mpr hh
    linarith only [hh']
  have hlog : 0 ≤ Real.log (B/A) := Real.log_nonneg ((one_le_div hA0).mpr hAB)
  have hbase : 0 ≤ ((2:ℝ)^p-1)⁻¹+(1-(2:ℝ)^(-q))⁻¹+2 := by positivity
  have hnumber : ((2:ℝ)^p-1)⁻¹+(L:ℝ)+(1-(2:ℝ)^(-q))⁻¹ ≤ constant p q*(1+Real.log (B/A)) := by
    unfold constant
    have hm := mul_nonneg hbase hlog
    have hi : 0 ≤ (Real.log 2)⁻¹ := by positivity
    change (L:ℝ) ≤ 2+Real.log (B/A)*(Real.log 2)⁻¹ at hL
    nlinarith only [hL,hm,hi]
  refine ⟨hs,?_⟩
  rw [← hs.sum_add_tsum_nat_add (M+1),← hcut,sum_range_add]
  have hh := add_le_add (add_le_add hprefix hmiddle') htail
  have hm := mul_le_mul_of_nonneg_left hnumber hC
  rw [hcut]
  have hh' : (∑ n ∈ range N,g n)+(∑ n ∈ range L,g (n+N))+(∑' n,g (n+(M+1))) ≤
      C*(((2:ℝ)^p-1)⁻¹+(L:ℝ)+(1-(2:ℝ)^(-q))⁻¹) := hh.trans_eq (by ring)
  have he : C*(constant p q*(1+Real.log (B/A))) = C*constant p q*(1+Real.log (B/A)) := by ring
  have hh'' := hh'.trans (hm.trans_eq he)
  simpa only [Nat.add_comm] using! hh''

end SHE.ThreeBandSeries
