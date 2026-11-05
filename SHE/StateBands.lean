module

public import SHE.DyadicTransport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.StateBands

def rootTerm (α m : ℝ) (n : ℕ) :=
  ((2:ℝ)^n)^(-α) * min 1 (m*(2:ℝ)^n)

def geometricConstant (q : ℝ) := (1-(2:ℝ)^(-q))⁻¹
def rootConstant (α : ℝ) := DyadicTransport.smoothingConstant (1-α) + geometricConstant α

theorem geometric_ratio {q : ℝ} (hq : 0 < q) : 0 < (2:ℝ)^(-q) ∧ (2:ℝ)^(-q) < 1 := by
  refine ⟨by positivity, ?_⟩
  simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) (by linarith : -q<0)

theorem geometric_bands {q R : ℝ} (hq : 0 < q) (hR : 0 < R) :
    Summable (fun n : ℕ => (R*(2:ℝ)^n)^(-q)) ∧
      (∑' n : ℕ, (R*(2:ℝ)^n)^(-q)) = geometricConstant q * R^(-q) := by
  have hr := geometric_ratio hq
  have he (n : ℕ) : (R*(2:ℝ)^n)^(-q) = R^(-q)*((2:ℝ)^(-q))^n := by
    rw [Real.mul_rpow hR.le (by positivity), Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
  have hs := (summable_geometric_of_lt_one hr.1.le hr.2).mul_left (R^(-q))
  simp only [← he] at hs
  refine ⟨hs, ?_⟩
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr.1.le hr.2]
  dsimp [geometricConstant]
  ring

theorem rootTerm_identity {m : ℝ} (hm : 0 < m) (α : ℝ) (n : ℕ) :
    rootTerm α m n = m * DyadicTransport.smoothingTerm (1/m) (1-α) n := by
  let b : ℝ := (2:ℝ)^n
  have hb : 0 < b := by dsimp [b]; positivity
  have hclip : min 1 (m*b) = m*b*min 1 ((1/m)/b) := by
    by_cases hmb : m*b ≤ 1
    · rw [min_eq_right hmb, min_eq_left ((le_div_iff₀ hb).mpr ((le_div_iff₀ hm).mpr (by nlinarith [hmb])))]
      ring
    · have hratio : (1/m)/b ≤ 1 := by
        apply (div_le_one hb).mpr
        apply (div_le_iff₀ hm).mpr
        nlinarith [le_of_lt (lt_of_not_ge hmb)]
      rw [min_eq_left (le_of_lt (lt_of_not_ge hmb)), min_eq_right hratio]
      field_simp
  change b^(-α)*min 1 (m*b) = m*(min 1 ((1/m)/b)*b^(1-α))
  rw [hclip, show 1-α = 1+(-α) by ring, Real.rpow_add hb, Real.rpow_one]
  ring

/-- The annular root minimum sums to exactly the fractional state
power required by the Gaussian row, over the full infinite band sum. -/
theorem root_bands {α m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hm : 0 ≤ m) :
    Summable (rootTerm α m) ∧ (∑' n, rootTerm α m n) ≤ rootConstant α * m^α := by
  have hc0 : 0 ≤ geometricConstant α := by
    dsimp [geometricConstant]
    exact inv_nonneg.mpr (by linarith [(geometric_ratio hα0).2])
  have hs0 : 0 ≤ DyadicTransport.smoothingConstant (1-α) :=
    (DyadicTransport.smoothingConstant_pos (by linarith) (by linarith)).le
  by_cases hm0 : m=0
  · subst m
    have he : rootTerm α 0 = fun _ => 0 := by funext n; simp [rootTerm]
    rw [he]
    simp [Real.zero_rpow (ne_of_gt hα0)]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  by_cases hm1 : m ≤ 1
  · have hA : 1 ≤ 1/m := (le_div_iff₀ hmpos).mpr (by simpa using hm1)
    have hs := DyadicTransport.smoothing_series hA (by linarith : 0<1-α) (by linarith : 1-α<1)
    have he := rootTerm_identity hmpos α
    have hsum : Summable (rootTerm α m) := (hs.1.mul_left m).congr (fun n => (he n).symm)
    refine ⟨hsum, ?_⟩
    have hp : m*(1/m)^(1-α) = m^α := by
      rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
      calc
        _ = m ^ ((1:ℝ) + -(1-α)) := by
          simpa only [Real.rpow_one] using (Real.rpow_add hmpos (1:ℝ) (-(1-α))).symm
        _ = _ := by congr 1; ring
    calc
      _ = m*∑' n, DyadicTransport.smoothingTerm (1/m) (1-α) n := by simp_rw [he]; exact tsum_mul_left
      _ ≤ m*(DyadicTransport.smoothingConstant (1-α)*(1/m)^(1-α)) := mul_le_mul_of_nonneg_left hs.2 hm
      _ = DyadicTransport.smoothingConstant (1-α)*(m*(1/m)^(1-α)) := by ring
      _ = DyadicTransport.smoothingConstant (1-α)*m^α := by rw [hp]
      _ ≤ _ := by dsimp [rootConstant]; nlinarith [Real.rpow_nonneg hm α]
  · have hgeo := geometric_bands hα0 (by norm_num : (0:ℝ)<1)
    simp only [one_mul] at hgeo
    have hmajor : ∀ n, rootTerm α m n ≤ ((2:ℝ)^n)^(-α) := by
      intro n
      exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (mul_one _)
    have hs : Summable (rootTerm α m) := Summable.of_nonneg_of_le
      (fun n => by dsimp [rootTerm]; positivity) hmajor hgeo.1
    refine ⟨hs, ?_⟩
    have hmα : 1 ≤ m^α := Real.one_le_rpow (le_of_lt (lt_of_not_ge hm1)) hα0.le
    have hc : 0 ≤ rootConstant α := add_nonneg hs0 hc0
    calc
      _ ≤ ∑' n, ((2:ℝ)^n)^(-α) := hs.tsum_le_tsum hmajor hgeo.1
      _ = geometricConstant α := by simpa using hgeo.2
      _ ≤ rootConstant α := by dsimp [rootConstant]; linarith
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hmα hc]

end SHE.StateBands

namespace SHE.StateBands

/-- Arbitrary positive high-frequency cutoffs retain the same
fractional root state power after the full infinite band summation. -/
theorem scaled_root_bands {α m R : ℝ}
    (hα0 : 0<α) (hα1 : α<1) (hm : 0≤m) (hR : 0<R) :
    Summable (fun n : ℕ => (R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n))) ∧
      (∑' n : ℕ, (R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n))) ≤ rootConstant α*m^α := by
  have hh := root_bands hα0 hα1 (mul_nonneg hR.le hm)
  have he (n : ℕ) : (R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n)) =
      R^(-α)*rootTerm α (R*m) n := by
    rw [Real.mul_rpow hR.le (by positivity)]
    unfold rootTerm
    rw [show m*(R*(2:ℝ)^n)=(R*m)*(2:ℝ)^n by ring]
    ring
  have hs : Summable (fun n : ℕ => (R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n))) :=
    (hh.1.mul_left (R^(-α))).congr (fun n => (he n).symm)
  refine ⟨hs, ?_⟩
  have hp : R^(-α)*(R*m)^α=m^α := by
    rw [Real.mul_rpow hR.le hm,← mul_assoc,← Real.rpow_add hR,neg_add_cancel,Real.rpow_zero,one_mul]
  calc
    _ = R^(-α)*∑' n, rootTerm α (R*m) n := by simp_rw [he]; exact tsum_mul_left
    _ ≤ R^(-α)*(rootConstant α*(R*m)^α) :=
      mul_le_mul_of_nonneg_left hh.2 (Real.rpow_nonneg hR.le _)
    _ = rootConstant α*(R^(-α)*(R*m)^α) := by ring
    _ = _ := by rw [hp]

/-- The numerical band ledger applies to genuine Banach-space
contributions. Absolute convergence and the norm bound are conclusions. -/
theorem vector_geometric_bands {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {q R C : ℝ} (hq : 0<q) (hR : 0<R) (_hC : 0≤C) (v : ℕ → V)
    (hv : ∀ n, ‖v n‖ ≤ C*(R*(2:ℝ)^n)^(-q)) :
    Summable v ∧ ‖∑' n, v n‖ ≤ C*geometricConstant q*R^(-q) := by
  have hs := geometric_bands hq hR
  have hmajor := hs.1.mul_left C
  refine ⟨Summable.of_norm_bounded hmajor hv, ?_⟩
  calc
    _ ≤ ∑' n, C*(R*(2:ℝ)^n)^(-q) := tsum_of_norm_bounded hmajor.hasSum hv
    _ = _ := by rw [tsum_mul_left,hs.2]; ring

theorem vector_root_bands {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {α m R C : ℝ} (hα0 : 0<α) (hα1 : α<1) (hm : 0≤m) (hR : 0<R)
    (hC : 0≤C) (v : ℕ → V)
    (hv : ∀ n, ‖v n‖ ≤ C*((R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n)))) :
    Summable v ∧ ‖∑' n, v n‖ ≤ C*rootConstant α*m^α := by
  have hs := scaled_root_bands hα0 hα1 hm hR
  have hmajor := hs.1.mul_left C
  refine ⟨Summable.of_norm_bounded hmajor hv, ?_⟩
  calc
    _ ≤ ∑' n, C*((R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n))) :=
      tsum_of_norm_bounded hmajor.hasSum hv
    _ = C*∑' n, (R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n)) := tsum_mul_left
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs.2 hC

end SHE.StateBands
