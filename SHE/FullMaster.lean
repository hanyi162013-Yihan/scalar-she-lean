module

public import SHE.Closure
public import SHE.Algebra

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open Filter Topology

/-! The printed master inequality retains two different linear slots.
This file verifies their eventual absorption, including arbitrary fixed
logarithmic powers and the actual finite sum over predictable orders.
The analytic master inequality itself remains an explicit hypothesis. -/

/-- Every fixed logarithmic power is dominated by every positive power. -/
theorem logPower_mul_rpow_tends_zero {a : ℝ} (ha : 0 < a) (d : ℕ) :
    Tendsto (fun Λ : ℝ => (1 + Real.log Λ) ^ d * Λ ^ (-a)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun Λ : ℝ => Real.log Λ ^ d * Λ ^ (-a)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (d : ℝ) ha).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
    simp only [Real.rpow_natCast, div_eq_mul_inv, Real.rpow_neg hΛ.le]
  apply squeeze_zero' ?_ ?_ (by simpa using hbase.const_mul ((2 : ℝ) ^ d))
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with Λ hΛ
    have hΛ0 : 0 < Λ := lt_of_lt_of_le (Real.exp_pos 1) hΛ
    have hlog : 1 ≤ Real.log Λ := (Real.le_log_iff_exp_le hΛ0).mpr hΛ
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with Λ hΛ
    have hΛ0 : 0 < Λ := lt_of_lt_of_le (Real.exp_pos 1) hΛ
    have hlog : 1 ≤ Real.log Λ := (Real.le_log_iff_exp_le hΛ0).mpr hΛ
    have hp : (1 + Real.log Λ) ^ d ≤ (2 * Real.log Λ) ^ d :=
      pow_le_pow_left₀ (by linarith) (by linarith) d
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hΛ0.le (-a))

theorem rpow_tends_zero_of_neg {a : ℝ} (ha : a < 0) :
    Tendsto (fun Λ : ℝ => Λ ^ a) atTop (𝓝 0) := by
  simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr ha)

def linearK (β : ℝ) (d : ℕ) (Λ : ℝ) : ℝ :=
  Λ ^ (-w β 2 / 4) + (1 + Real.log Λ) ^ d * Λ ^ (-β / 4)

def linearM (β : ℝ) (N : ℕ) (Λ : ℝ) : ℝ :=
  1 + Λ ^ (-rho β / 2 + (1 - β) / 4) + Λ ^ (-qGamma β / 4) +
    Λ ^ (-qProfile β 2 / 4) +
    Λ ^ (-rho β / 2) * ∑ j ∈ Finset.Icc 2 (N + 1), Λ ^ (-p β j / 4)

def energyScale (β Λ : ℝ) := Λ ^ (rho β / 2 - 1 / 4)

theorem linearK_tends_zero {β : ℝ} (hβ : 0 < β) (d : ℕ) :
    Tendsto (linearK β d) atTop (𝓝 0) := by
  have hw : 0 < w β 2 / 4 := by rw [w_two]; positivity
  change Tendsto (fun Λ : ℝ => Λ ^ (-w β 2 / 4) + (1 + Real.log Λ) ^ d * Λ ^ (-β / 4)) atTop (𝓝 0)
  simpa only [neg_div, add_zero] using
    (tendsto_rpow_neg_atTop hw).add (logPower_mul_rpow_tends_zero (by linarith : 0 < β / 4) d)

theorem energyScale_mul_linearM {β Λ : ℝ} (N : ℕ) (hΛ : 0 < Λ) :
    energyScale β Λ * linearM β N Λ =
      Λ ^ (rho β / 2 - 1 / 4) + Λ ^ (-β / 4) +
      Λ ^ (rho β / 2 - 1 / 4 - qGamma β / 4) +
      Λ ^ (rho β / 2 - 1 / 4 - qProfile β 2 / 4) +
      ∑ j ∈ Finset.Icc 2 (N + 1), Λ ^ (-1 / 4 - p β j / 4) := by
  unfold energyScale linearM
  simp only [mul_add, mul_one, ← Real.rpow_add hΛ, Finset.mul_sum]
  congr 2 <;> try ring_nf

/-- The finite predictable sum and the low-band linear coefficient all
vanish after the stochastic energy scaling. -/
theorem scaled_linearM_tends_zero {β : ℝ} (hβ : 0 < β) (hsmall : β ≤ 4 / 25)
    (N : ℕ) :
    Tendsto (fun Λ => energyScale β Λ * linearM β N Λ) atTop (𝓝 0) := by
  have had := admissible_parameters β hβ hsmall
  have hd := all_degrees_positive β hβ hsmall
  have hρ : rho β / 2 - 1 / 4 < 0 := by linarith [had.2.1]
  have h1 : Tendsto (fun Λ : ℝ => Λ ^ (rho β / 2 - 1 / 4)) atTop (𝓝 0) :=
    rpow_tends_zero_of_neg hρ
  have h2 : Tendsto (fun Λ : ℝ => Λ ^ (-β / 4)) atTop (𝓝 0) :=
    rpow_tends_zero_of_neg (by linarith)
  have h3 : Tendsto (fun Λ : ℝ => Λ ^ (rho β / 2 - 1 / 4 - qGamma β / 4)) atTop (𝓝 0) :=
    rpow_tends_zero_of_neg (by linarith [hd.1])
  have h4 : Tendsto (fun Λ : ℝ => Λ ^ (rho β / 2 - 1 / 4 - qProfile β 2 / 4)) atTop (𝓝 0) :=
    rpow_tends_zero_of_neg (by linarith [hd.2.2.2.1])
  have hsum : Tendsto
      (fun Λ : ℝ => ∑ j ∈ Finset.Icc 2 (N + 1), Λ ^ (-1 / 4 - p β j / 4)) atTop (𝓝 0) := by
    have hh : ∀ j ∈ Finset.Icc 2 (N + 1),
        Tendsto (fun Λ : ℝ => Λ ^ (-1 / 4 - p β j / 4)) atTop (𝓝 0) := by
      intro j hj
      have hjp := all_predictable_degrees_positive β hβ j (Finset.mem_Icc.mp hj).1
      exact rpow_tends_zero_of_neg (by linarith)
    simpa using tendsto_finsetSum _ hh
  have ht := (((h1.add h2).add h3).add h4).add hsum
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  exact (energyScale_mul_linearM N hΛ).symm

theorem full_linear_coefficient_tends_zero {β C : ℝ}
    (hβ : 0 < β) (hsmall : β ≤ 4 / 25) (N d : ℕ) :
    Tendsto (fun Λ => C * linearK β d Λ + C ^ 2 * energyScale β Λ * linearM β N Λ)
      atTop (𝓝 0) := by
  simpa only [mul_assoc, mul_zero, add_zero] using
    ((linearK_tends_zero hβ d).const_mul C).add
      ((scaled_linearM_tends_zero hβ hsmall N).const_mul (C ^ 2))

def nonlinearRows (β Λ m : ℝ) :=
  m ^ alpha β + Λ ^ (-qNative β 2 / 4) * m ^ chi β +
    Λ ^ (-rho β / 2 - (W β (depth β) - chiR β) / 4) * m ^ chiR β

/-- The actual full master inequality, with `R=Λ^(1/4)` written in
flattened powers of Λ. Its truth for SPDE energies is not asserted here. -/
def FullMaster (β C Λ K m err : ℝ) (d : ℕ) : Prop :=
  K ≤ C * (linearK β d Λ * K + linearM β (depth β) Λ * m + nonlinearRows β Λ m) + err

theorem linearM_nonneg {β Λ : ℝ} (N : ℕ) (hΛ : 0 ≤ Λ) : 0 ≤ linearM β N Λ := by
  unfold linearM
  positivity

/-- Absorption acts on the unsquared master and retains both linear rows. -/
theorem full_master_absorbed {β C Λ K m err : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K)
    (henergy : m ≤ C * energyScale β Λ * K)
    (hsmall : C * linearK β d Λ + C ^ 2 * energyScale β Λ * linearM β (depth β) Λ ≤ 1 / 2)
    (hmaster : FullMaster β C Λ K m err d) :
    m ≤ 2 * C ^ 2 * (energyScale β Λ * nonlinearRows β Λ m) +
      2 * C * energyScale β Λ * err := by
  have hs : 0 ≤ energyScale β Λ := Real.rpow_nonneg hΛ _
  have hm' : m ≤ (C * energyScale β Λ) * K := henergy
  have hb : 0 ≤ C * linearM β (depth β) Λ := mul_nonneg hC (linearM_nonneg _ hΛ)
  have hK' : K ≤ (C * linearK β d Λ) * K +
      (C * linearM β (depth β) Λ) * m + (C * nonlinearRows β Λ m + err) := by
    simpa only [FullMaster, mul_add, mul_assoc, add_assoc] using hmaster
  have hsmall' : C * linearK β d Λ + (C * linearM β (depth β) Λ) *
      (C * energyScale β Λ) ≤ 1 / 2 := by nlinarith only [hsmall]
  have hbound := absorb_two_linear_slots hK' hm' hb hsmall' hK
  calc
    m ≤ (C * energyScale β Λ) * K := henergy
    _ ≤ (C * energyScale β Λ) * (2 * (C * nonlinearRows β Λ m + err)) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hC hs)
    _ = _ := by ring

theorem scaled_nonlinearRows {β Λ m : ℝ} (hΛ : 0 < Λ) :
    energyScale β Λ * nonlinearRows β Λ m =
      Λ ^ (-(aGaussian β / 2)) * m ^ alpha β +
      Λ ^ (-(aNative β / 2)) * m ^ chi β +
      Λ ^ (-(aRemainder β / 2)) * m ^ chiR β := by
  unfold energyScale nonlinearRows aGaussian aNative aRemainder
  simp only [mul_add, ← mul_assoc, ← Real.rpow_add hΛ]
  have e₁ : rho β / 2 - 1 / 4 = -((1 / 2 - rho β) / 2) := by ring
  have e₂ : rho β / 2 - 1 / 4 + -qNative β 2 / 4 =
      -((1 / 2 - rho β + 2 * (1 / 4) * qNative β 2) / 2) := by ring
  have e₃ : rho β / 2 - 1 / 4 + (-rho β / 2 - (W β (depth β) - chiR β) / 4) =
      -((1 / 2 + 2 * (1 / 4) * (W β (depth β) - chiR β)) / 2) := by ring
  rw [e₂, e₃, e₁]

theorem half_rate {a z : ℝ} (hr : (5 / 2 : ℝ) < a / (1 - z)) :
    -(a / 2) / (1 - z) ≤ -(5 / 4 : ℝ) := by
  have he : -(a / 2) / (1 - z) = -(a / (1 - z)) / 2 := by ring
  rw [he]
  linarith

def fullMasterConstant (β C : ℝ) :=
  (8 * C ^ 2) ^ (1 / (1 - alpha β)) +
    (8 * C ^ 2) ^ (1 / (1 - chi β)) +
    (8 * C ^ 2) ^ (1 / (1 - chiR β)) + 8 * C

/-- The full, zero-loss master gives the claimed decay once its two
linear coefficients are small. A deterministic diagonal error Λ⁻²
already suffices at the unsquared level. -/
theorem full_master_decay {β C Λ K m err : ℝ} {d : ℕ}
    (hβ : 0 < β) (hβsmall : β ≤ 4 / 25) (hC : 0 ≤ C)
    (hΛ : 1 ≤ Λ) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (henergy : m ≤ C * energyScale β Λ * K)
    (hsmall : C * linearK β d Λ + C ^ 2 * energyScale β Λ * linearM β (depth β) Λ ≤ 1 / 2)
    (herr : err ≤ Λ ^ (-(2 : ℝ)))
    (hmaster : FullMaster β C Λ K m err d) :
    m ≤ fullMasterConstant β C * Λ ^ (-(5 / 4 : ℝ)) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have had := admissible_parameters β hβ hβsmall
  have hz₁ : alpha β < 1 := had.2.2.2.2.2.1
  have hz₂ : chi β < 1 := lt_of_lt_of_le had.2.2.2.2.2.2.2.1 (min_le_left _ _)
  have hz₃ : chiR β < 1 := lt_trans had.2.2.2.2.2.2.2.2.2 (by linarith : β < 1)
  have hs0 : 0 ≤ energyScale β Λ := Real.rpow_nonneg hΛpos.le _
  have hs1 : energyScale β Λ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith [had.2.1])
  have htail : 2 * C * energyScale β Λ * err ≤ 2 * C * Λ ^ (-(2 : ℝ)) := by
    calc
      _ ≤ 2 * C * energyScale β Λ * Λ ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs1 (mul_nonneg hC (Real.rpow_nonneg hΛpos.le (-(2 : ℝ))))]
  have hab := full_master_absorbed hC hΛpos.le hK henergy hsmall hmaster
  rw [scaled_nonlinearRows hΛpos] at hab
  have hrow : m ≤ (2 * C ^ 2) * Λ ^ (-(aGaussian β / 2)) * m ^ alpha β +
      (2 * C ^ 2) * Λ ^ (-(aNative β / 2)) * m ^ chi β +
      (2 * C ^ 2) * Λ ^ (-(aRemainder β / 2)) * m ^ chiR β + 2 * C * Λ ^ (-(2 : ℝ)) := by
    nlinarith only [hab, htail]
  have hb := three_row_decay hm hΛ (by positivity : 0 ≤ 2 * C ^ 2)
    (by positivity : 0 ≤ 2 * C * Λ ^ (-(2 : ℝ))) hz₁ hz₂ hz₃ hrow
  have hr := all_rates_exceed_target β hβ hβsmall
  have hp₁ : Λ ^ (-(aGaussian β / 2) / (1 - alpha β)) ≤ Λ ^ (-(5 / 4 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hΛ
    exact half_rate hr.1
  have hp₂ : Λ ^ (-(aNative β / 2) / (1 - chi β)) ≤ Λ ^ (-(5 / 4 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hΛ
    exact half_rate hr.2.1
  have hp₃ : Λ ^ (-(aRemainder β / 2) / (1 - chiR β)) ≤ Λ ^ (-(5 / 4 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hΛ
    exact half_rate hr.2.2
  have hp₄ : Λ ^ (-(2 : ℝ)) ≤ Λ ^ (-(5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hΛ (by norm_num)
  have hb₁ := mul_le_mul_of_nonneg_left hp₁
    (Real.rpow_nonneg (by positivity : 0 ≤ 4 * (2 * C ^ 2)) (1 / (1 - alpha β)))
  have hb₂ := mul_le_mul_of_nonneg_left hp₂
    (Real.rpow_nonneg (by positivity : 0 ≤ 4 * (2 * C ^ 2)) (1 / (1 - chi β)))
  have hb₃ := mul_le_mul_of_nonneg_left hp₃
    (Real.rpow_nonneg (by positivity : 0 ≤ 4 * (2 * C ^ 2)) (1 / (1 - chiR β)))
  have hb₄ := mul_le_mul_of_nonneg_left hp₄ (by positivity : 0 ≤ 8 * C)
  dsimp [fullMasterConstant]
  have hc : 4 * (2 * C ^ 2) = 8 * C ^ 2 := by ring
  rw [hc] at hb hb₁ hb₂ hb₃
  nlinarith only [hb, hb₁, hb₂, hb₃, hb₄]

/-- The integrated square energy has the manuscript's Λ⁻⁵⸍² decay. -/
theorem full_master_square_energy_decay {β C Λ K m err : ℝ} {d : ℕ}
    (hβ : 0 < β) (hβsmall : β ≤ 4 / 25) (hC : 0 ≤ C)
    (hΛ : 1 ≤ Λ) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (henergy : m ≤ C * energyScale β Λ * K)
    (hsmall : C * linearK β d Λ + C ^ 2 * energyScale β Λ * linearM β (depth β) Λ ≤ 1 / 2)
    (herr : err ≤ Λ ^ (-(2 : ℝ)))
    (hmaster : FullMaster β C Λ K m err d) :
    m ^ (2 : ℕ) ≤ fullMasterConstant β C ^ (2 : ℕ) * Λ ^ (-(5 / 2 : ℝ)) := by
  have hb := full_master_decay hβ hβsmall hC hΛ hK hm henergy hsmall herr hmaster
  have hs := pow_le_pow_left₀ hm hb 2
  have hΛ0 : 0 ≤ Λ := by linarith
  calc
    _ ≤ (fullMasterConstant β C * Λ ^ (-(5 / 4 : ℝ))) ^ (2 : ℕ) := hs
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hΛ0]
      norm_num

/-- No linear-coefficient smallness needs to be assumed: it follows
eventually from the printed parameters, at every fixed logarithmic order. -/
theorem full_master_eventual_energy_decay {β C : ℝ} {K m err : ℝ → ℝ} (d : ℕ)
    (hβ : 0 < β) (hβsmall : β ≤ 4 / 25) (hC : 0 ≤ C)
    (h : ∀ᶠ Λ in atTop, 0 ≤ K Λ ∧ 0 ≤ m Λ ∧
      m Λ ≤ C * energyScale β Λ * K Λ ∧ err Λ ≤ Λ ^ (-(2 : ℝ)) ∧
      FullMaster β C Λ (K Λ) (m Λ) (err Λ) d) :
    ∀ᶠ Λ in atTop, 0 ≤ m Λ ^ (2 : ℕ) ∧
      m Λ ^ (2 : ℕ) ≤ fullMasterConstant β C ^ (2 : ℕ) * Λ ^ (-(5 / 2 : ℝ)) := by
  have ht := full_linear_coefficient_tends_zero (C := C) hβ hβsmall (depth β) d
  have hsmall := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [h, hsmall, eventually_ge_atTop (1 : ℝ)] with Λ hΛ hs hΛ1
  exact ⟨sq_nonneg _, full_master_square_energy_decay hβ hβsmall hC hΛ1 hΛ.1 hΛ.2.1
    hΛ.2.2.1 hs.le hΛ.2.2.2.1 hΛ.2.2.2.2⟩

/-- The final damping cost vanishes directly from the full master.
All stochastic construction and analytic estimates remain visible in `h`. -/
theorem full_master_cost_limit {β C : ℝ} {K m err : ℝ → ℝ} (d : ℕ)
    (hβ : 0 < β) (hβsmall : β ≤ 4 / 25) (hC : 0 ≤ C)
    (h : ∀ᶠ Λ in atTop, 0 ≤ K Λ ∧ 0 ≤ m Λ ∧
      m Λ ≤ C * energyScale β Λ * K Λ ∧ err Λ ≤ Λ ^ (-(2 : ℝ)) ∧
      FullMaster β C Λ (K Λ) (m Λ) (err Λ) d) :
    Tendsto (fun Λ => Λ ^ (2 : ℕ) * m Λ ^ (2 : ℕ)) atTop (𝓝 0) := by
  exact damping_cost_tends_to_zero (p := (5 / 2 : ℝ)) (by norm_num)
    (full_master_eventual_energy_decay d hβ hβsmall hC h)

end SHE
