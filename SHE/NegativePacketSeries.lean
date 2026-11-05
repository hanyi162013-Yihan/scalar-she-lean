module

public import SHE.DyadicPowerSeries

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NegativePacketSeries
open DyadicPowerSeries

def constant (ρ : ℝ) : ℝ := DyadicPowerSeries.constant (1-2*ρ) (3-4*ρ)

theorem constant_pos {ρ : ℝ} (hρ : ρ < 1/2) : 0 < constant ρ :=
  DyadicPowerSeries.constant_pos (by linarith) (by linarith)

theorem coarse_identity {ρ t : ℝ} (ht : 0 < t) (n : ℕ)
    (hn : (2:ℝ)^n ≤ t^(-(1/2:ℝ))) :
    t^(-ρ)*term (t^(-(1/2:ℝ))) (1-2*ρ) (3-4*ρ) n=
      t^(-ρ)*((2:ℝ)^n)^(1-2*ρ) := by
  unfold term
  rw [min_eq_left ((one_le_div (by positivity : (0:ℝ) < 2^n)).mpr hn),Real.one_rpow,one_mul]

theorem fine_identity {ρ t : ℝ} (ht : 0 < t) (n : ℕ)
    (hn : t^(-(1/2:ℝ)) ≤ (2:ℝ)^n) :
    t^(-ρ)*term (t^(-(1/2:ℝ))) (1-2*ρ) (3-4*ρ) n=
      t^(ρ-3/2)*((2:ℝ)^n)^(2*ρ-2) := by
  have hD : 0 < (2:ℝ)^n := by positivity
  unfold term
  rw [min_eq_right ((div_le_one hD).mpr hn),Real.div_rpow (Real.rpow_nonneg ht.le _) hD.le,
    ← Real.rpow_mul ht.le,div_eq_mul_inv,← Real.rpow_neg hD.le]
  calc
    _ = (t^(-ρ)*t^((-(1/2:ℝ))*(3-4*ρ)))*
        (((2:ℝ)^n)^(-(3-4*ρ))*((2:ℝ)^n)^(1-2*ρ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add ht,← Real.rpow_add hD]
      congr 2 <;> ring

/-- Coarse/fine actual generation bounds sum to the sharp heat power.
Only the two branch estimates are hypotheses; the entire infinite
dyadic summation and exponent cancellation are proved. -/
theorem series {ρ t C : ℝ} (hρ : ρ < 1/2) (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : 0 ≤ C) (g : ℕ → ℝ) (hg : ∀ n,0 ≤ g n)
    (hcoarse : ∀ n,(2:ℝ)^n ≤ t^(-(1/2:ℝ)) → g n ≤ C*t^(-ρ)*((2:ℝ)^n)^(1-2*ρ))
    (hfine : ∀ n,t^(-(1/2:ℝ)) ≤ (2:ℝ)^n → g n ≤ C*t^(ρ-3/2)*((2:ℝ)^n)^(2*ρ-2)) :
    Summable g ∧ (∑' n,g n) ≤ C*constant ρ*t^(-(1/2:ℝ)) := by
  have hA : 1 ≤ t^(-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hs := DyadicPowerSeries.series hA (by linarith : 0 < 1-2*ρ) (by linarith : 1-2*ρ < 3-4*ρ)
  have hdom (n : ℕ) : g n ≤ (C*t^(-ρ))*term (t^(-(1/2:ℝ))) (1-2*ρ) (3-4*ρ) n := by
    rcases le_total ((2:ℝ)^n) (t^(-(1/2:ℝ))) with hn | hn
    · rw [mul_assoc,coarse_identity ht n hn,← mul_assoc]
      exact hcoarse n hn
    · rw [mul_assoc,fine_identity ht n hn,← mul_assoc]
      exact hfine n hn
  have hmajor := hs.1.mul_left (C*t^(-ρ))
  have hsum := Summable.of_nonneg_of_le hg hdom hmajor
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' n,(C*t^(-ρ))*term (t^(-(1/2:ℝ))) (1-2*ρ) (3-4*ρ) n :=
      hsum.tsum_le_tsum hdom hmajor
    _ = (C*t^(-ρ))*(∑' n,term (t^(-(1/2:ℝ))) (1-2*ρ) (3-4*ρ) n) := tsum_mul_left
    _ ≤ (C*t^(-ρ))*(DyadicPowerSeries.constant (1-2*ρ) (3-4*ρ)*(t^(-(1/2:ℝ)))^(1-2*ρ)) :=
      mul_le_mul_of_nonneg_left hs.2 (mul_nonneg hC (Real.rpow_nonneg ht.le _))
    _ = _ := by
      rw [← Real.rpow_mul ht.le]
      calc
        _ = C*constant ρ*(t^(-ρ)*t^((-(1/2:ℝ))*(1-2*ρ))) := by unfold constant; ring
        _ = _ := by rw [← Real.rpow_add ht]; congr 2; ring

end SHE.NegativePacketSeries
