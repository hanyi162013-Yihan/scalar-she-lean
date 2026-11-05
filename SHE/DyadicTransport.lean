module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
namespace DyadicTransport
open Finset

/-- The heat-cancellation weight at a dyadic cutoff. -/
def weight (N n : ℕ) : ℝ := min 1 ((2 : ℝ) ^ N / 2 ^ n)
def constant (q : ℝ) := (q - 1)⁻¹ + (1 - q / 2)⁻¹

theorem weight_nonneg (N n : ℕ) : 0 ≤ weight N n := by
  unfold weight
  positivity

theorem weight_coarse (N n : ℕ) (hn : n < N) : weight N n = 1 := by
  unfold weight
  apply min_eq_left
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
  simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn.le)

theorem weighted_tail (N n : ℕ) (q : ℝ) :
    weight N (n + N) * q ^ (n + N) = q ^ N * (q / 2) ^ n := by
  have hpow : (2 : ℝ) ^ N ≤ 2 ^ (n + N) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hratio : (2 : ℝ) ^ N / 2 ^ (n + N) ≤ 1 :=
    (div_le_one (by positivity)).mpr hpow
  rw [weight, min_eq_right hratio]
  simp only [pow_add, div_pow]
  field_simp

theorem weighted_summable (N : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq2 : q < 2) :
    Summable (fun n => weight N n * q ^ n) := by
  apply (summable_nat_add_iff N).mp
  simp_rw [weighted_tail]
  exact (summable_geometric_of_lt_one (by positivity : 0 ≤ q / 2) (by linarith : q / 2 < 1)).mul_left _

/-- Exact coarse/fine geometric sum behind the signed heat estimate. -/
theorem weighted_tsum (N : ℕ) {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    (∑' n, weight N n * q ^ n) =
      (q ^ N - 1) / (q - 1) + q ^ N / (1 - q / 2) := by
  have hs := weighted_summable N (by linarith : 0 ≤ q) hq2
  rw [← hs.sum_add_tsum_nat_add N]
  have hc : (∑ n ∈ range N, weight N n * q ^ n) = (q ^ N - 1) / (q - 1) := by
    calc
      _ = ∑ n ∈ range N, q ^ n := by
        apply sum_congr rfl
        intro n hn
        rw [weight_coarse N n (mem_range.mp hn), one_mul]
      _ = _ := geom_sum_eq (ne_of_gt hq1) N
  rw [hc]
  simp_rw [weighted_tail]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity : 0 ≤ q / 2) (by linarith : q / 2 < 1)]
  rfl

theorem weighted_tsum_le (N : ℕ) {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    (∑' n, weight N n * q ^ n) ≤ constant q * q ^ N := by
  rw [weighted_tsum N hq1 hq2]
  have hcoarse : (q ^ N - 1) / (q - 1) ≤ q ^ N / (q - 1) := by
    apply div_le_div_of_nonneg_right (by linarith) (by linarith)
  calc
    _ ≤ q ^ N / (q - 1) + q ^ N / (1 - q / 2) := add_le_add hcoarse le_rfl
    _ = constant q * q ^ N := by unfold constant; simp only [div_eq_mul_inv]; ring

end DyadicTransport
end SHE

namespace SHE.DyadicTransport

open Finset

/-- A useful bound for moving a dyadic cutoff by at most one generation. -/
theorem min_one_le_two_min {a b : ℝ} (hab : a ≤ 2 * b) :
    min 1 a ≤ 2 * min 1 b := by
  by_cases hb : b ≤ 1
  · rw [min_eq_right hb]
    exact (min_le_right _ _).trans hab
  · rw [min_eq_left (by linarith : 1 ≤ b)]
    exact (min_le_left _ _).trans (by norm_num)

/-- Actual heat-generation series, with a non-dyadic inverse heat scale. -/
def smoothingTerm (A p : ℝ) (n : ℕ) : ℝ :=
  min 1 (A / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ p

def smoothingConstant (p : ℝ) := 2 * constant ((2 : ℝ) ^ p)

theorem smoothingConstant_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < smoothingConstant p := by
  have hq1 : 1 < (2 : ℝ) ^ p := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp0
    simpa using this
  have hq2 : (2 : ℝ) ^ p < 2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp1
    simpa using this
  unfold smoothingConstant constant
  have hd1 : 0 < (2 : ℝ) ^ p - 1 := by linarith
  have hd2 : 0 < 1 - (2 : ℝ) ^ p / 2 := by linarith
  positivity

/-- The precise geometric summability range is 0<p<1. -/
theorem smoothing_series {A p : ℝ} (hA : 1 ≤ A) (hp0 : 0 < p) (hp1 : p < 1) :
    Summable (smoothingTerm A p) ∧
      (∑' n, smoothingTerm A p n) ≤ smoothingConstant p * A ^ p := by
  obtain ⟨N,hNA,hAN⟩ := exists_nat_pow_near hA (by norm_num : (1 : ℝ) < 2)
  have hq1 : 1 < (2 : ℝ) ^ p := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp0
  have hq2 : (2 : ℝ) ^ p < 2 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp1
  have hmajor : ∀ n, smoothingTerm A p n ≤ 2 * (weight N n * ((2 : ℝ) ^ p) ^ n) := by
    intro n
    have hr : A / (2 : ℝ) ^ n ≤ 2 * ((2 : ℝ) ^ N / 2 ^ n) := by
      have he : A ≤ 2 * (2 : ℝ) ^ N := by rw [pow_succ] at hAN; linarith
      have := div_le_div_of_nonneg_right he (by positivity : (0 : ℝ) ≤ 2 ^ n)
      simpa only [mul_div_assoc] using this
    have hm := min_one_le_two_min hr
    have hp := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) p)
    simpa only [smoothingTerm, weight, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), mul_assoc] using hp
  have hsmajor := (weighted_summable N (by positivity : (0 : ℝ) ≤ 2 ^ p) hq2).mul_left 2
  have hs : Summable (smoothingTerm A p) :=
    Summable.of_nonneg_of_le (fun n => by unfold smoothingTerm; positivity) hmajor hsmajor
  refine ⟨hs, ?_⟩
  calc
    (∑' n, smoothingTerm A p n) ≤ ∑' n, 2 * (weight N n * ((2 : ℝ) ^ p) ^ n) :=
      hs.tsum_le_tsum hmajor hsmajor
    _ = 2 * ∑' n, weight N n * ((2 : ℝ) ^ p) ^ n := tsum_mul_left
    _ ≤ 2 * (constant ((2 : ℝ) ^ p) * ((2 : ℝ) ^ p) ^ N) :=
      mul_le_mul_of_nonneg_left (weighted_tsum_le N hq1 hq2) (by norm_num)
    _ = smoothingConstant p * ((2 : ℝ) ^ N) ^ p := by
      rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
      unfold smoothingConstant
      ring
    _ ≤ smoothingConstant p * A ^ p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hNA hp0.le)
        (smoothingConstant_pos hp0 hp1).le

/-- The massive inverse-inequality factor in the signed heat generation sum. -/
def massiveTerm (A Λ ρ : ℝ) (n : ℕ) : ℝ :=
  min 1 (A / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ (1 / 2 : ℝ) *
    (Λ + ((2 : ℝ) ^ n) ^ (2 : ℕ)) ^ (ρ / 2)

theorem massiveTerm_le {A Λ ρ : ℝ} (hA : 0 ≤ A) (hΛ : 0 ≤ Λ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (n : ℕ) :
    massiveTerm A Λ ρ n ≤ Λ ^ (ρ / 2) * smoothingTerm A (1 / 2) n +
      smoothingTerm A (1 / 2 + ρ) n := by
  have hbase : 0 < (2 : ℝ) ^ n := by positivity
  have hs := Real.rpow_add_le_add_rpow hΛ (sq_nonneg ((2 : ℝ) ^ n))
    (by linarith : 0 ≤ ρ / 2) (by linarith : ρ / 2 ≤ 1)
  have hmult : 0 ≤ min 1 (A / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ (1 / 2 : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left hs hmult
  have he : (((2 : ℝ) ^ n) ^ (2 : ℕ)) ^ (ρ / 2) = ((2 : ℝ) ^ n) ^ ρ := by
    rw [← Real.rpow_natCast_mul hbase.le]
    congr 1
    norm_num
    ring
  have hadd : ((2 : ℝ) ^ n) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ n) ^ ρ =
      ((2 : ℝ) ^ n) ^ (1 / 2 + ρ) := (Real.rpow_add hbase _ _).symm
  rw [he] at h
  dsimp [massiveTerm, smoothingTerm]
  calc
    _ ≤ min 1 (A / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ (1 / 2 : ℝ) *
        (Λ ^ (ρ / 2) + ((2 : ℝ) ^ n) ^ ρ) := h
    _ = Λ ^ (ρ / 2) * (min 1 (A / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ (1 / 2 : ℝ)) +
        min 1 (A / (2 : ℝ) ^ n) * (((2 : ℝ) ^ n) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ n) ^ ρ) := by ring
    _ = _ := by rw [hadd]

/-- Complete scalar generation summation for 0<rho<1/2. The operator-level
prefix and heat-cancellation bounds are separate, explicit analytic inputs. -/
theorem massive_series {A Λ ρ : ℝ} (hA : 1 ≤ A) (hΛ : 0 ≤ Λ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    Summable (massiveTerm A Λ ρ) ∧
      (∑' n, massiveTerm A Λ ρ n) ≤
        Λ ^ (ρ / 2) * smoothingConstant (1 / 2) * A ^ (1 / 2 : ℝ) +
        smoothingConstant (1 / 2 + ρ) * A ^ (1 / 2 + ρ) := by
  have hfirst := smoothing_series hA (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hsecond := smoothing_series hA (by linarith : (0 : ℝ) < 1 / 2 + ρ) (by linarith : 1 / 2 + ρ < 1)
  have hsmajor := (hfirst.1.mul_left (Λ ^ (ρ / 2))).add hsecond.1
  have hmajor := massiveTerm_le (by linarith : 0 ≤ A) hΛ hρ0.le (by linarith : ρ ≤ 1)
  have hs : Summable (massiveTerm A Λ ρ) :=
    Summable.of_nonneg_of_le (fun n => by dsimp [massiveTerm]; positivity) hmajor hsmajor
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, (Λ ^ (ρ / 2) * smoothingTerm A (1 / 2) n + smoothingTerm A (1 / 2 + ρ) n) :=
      hs.tsum_le_tsum hmajor hsmajor
    _ = Λ ^ (ρ / 2) * (∑' n, smoothingTerm A (1 / 2) n) +
        (∑' n, smoothingTerm A (1 / 2 + ρ) n) := by
      rw [Summable.tsum_add (hfirst.1.mul_left _) hsecond.1, tsum_mul_left]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hfirst.2 (Real.rpow_nonneg hΛ (ρ / 2))
      nlinarith [hsecond.2]

end SHE.DyadicTransport

namespace SHE.DyadicTransport

/-- A single constant for the two terms in the signed Haar heat estimate. -/
def signedHeatConstant (ρ : ℝ) := smoothingConstant (1 / 2) + smoothingConstant (1 / 2 + ρ)

/-- The full numerical heat-generation sum has exactly the two powers printed
in the manuscript's signed Haar heat estimate. Its constant depends only on rho. -/
theorem signed_heat_series {t Λ ρ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hΛ : 0 ≤ Λ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    Summable (massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ) ∧
      (∑' n, massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ n) ≤
        signedHeatConstant ρ *
          (Λ ^ (ρ / 2) * t ^ (-(1 / 4 : ℝ)) + t ^ (-(1 / 4 : ℝ) - ρ / 2)) := by
  have hA : 1 ≤ t ^ (-(1 / 2 : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have h := massive_series hA hΛ hρ0 hρ1
  have he1 : (t ^ (-(1 / 2 : ℝ))) ^ (1 / 2 : ℝ) = t ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    ring
  have he2 : (t ^ (-(1 / 2 : ℝ))) ^ (1 / 2 + ρ) = t ^ (-(1 / 4 : ℝ) - ρ / 2) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [he1, he2] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hc0 := (smoothingConstant_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).le
  have hc1 := (smoothingConstant_pos (by linarith : (0 : ℝ) < 1 / 2 + ρ) (by linarith : 1 / 2 + ρ < 1)).le
  have hn0 : 0 ≤ Λ ^ (ρ / 2) * t ^ (-(1 / 4 : ℝ)) := by positivity
  have hn1 : 0 ≤ t ^ (-(1 / 4 : ℝ) - ρ / 2) := by positivity
  dsimp [signedHeatConstant]
  nlinarith [mul_nonneg hc0 hn1, mul_nonneg hc1 hn0]

/-- Summation of actual nonnegative column contributions bounded generation
by generation. This does not assume the desired summed estimate. -/
theorem signed_heat_of_generation_bounds {t Λ ρ F : ℝ} {b : ℕ → ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hΛ : 0 ≤ Λ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hF : 0 ≤ F) (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ n, b n ≤ F * massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ n) :
    Summable b ∧ (∑' n, b n) ≤ F * signedHeatConstant ρ *
      (Λ ^ (ρ / 2) * t ^ (-(1 / 4 : ℝ)) + t ^ (-(1 / 4 : ℝ) - ρ / 2)) := by
  have hs := signed_heat_series ht ht1 hΛ hρ0 hρ1
  have hsmajor := hs.1.mul_left F
  have hsb := Summable.of_nonneg_of_le hb0 hb hsmajor
  refine ⟨hsb, ?_⟩
  calc
    _ ≤ ∑' n, F * massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ n := hsb.tsum_le_tsum hb hsmajor
    _ = F * ∑' n, massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ n := tsum_mul_left
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs.2 hF

end SHE.DyadicTransport
