module

public import SHE.FullMaster
public import SHE.FiniteFeedback

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open Filter Topology

/-- Every fixed logarithmic factor is covered by an arbitrarily small
permitted damping loss, after the finite comparison order is fixed. -/
theorem logPower_eventually_le_rpow {a : ℝ} (ha : 0 < a) (d : ℕ) :
    ∀ᶠ Λ : ℝ in atTop, (1+Real.log Λ) ^ d ≤ Λ ^ a := by
  have hh := (logPower_mul_rpow_tends_zero ha d).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hh, eventually_gt_atTop (0:ℝ)] with Λ hΛ hΛ0
  have hdiv : (1+Real.log Λ) ^ d / Λ ^ a < 1 := by
    simpa only [div_eq_mul_inv, Real.rpow_neg hΛ0.le] using hΛ
  have hb := (div_lt_iff₀ (Real.rpow_pos_of_pos hΛ0 a)).mp hdiv
  simpa only [one_mul] using hb.le

inductive MasterRow
  | gaussian | native | remainder
  deriving DecidableEq

instance : Fintype MasterRow :=
  ⟨{.gaussian, .native, .remainder}, by intro i; cases i <;> simp⟩

def rowExponent (β : ℝ) : MasterRow → ℝ
  | .gaussian => alpha β
  | .native => chi β
  | .remainder => chiR β

def rowDamping (β : ℝ) : MasterRow → ℝ
  | .gaussian => 0
  | .native => qNative β 2 / 4
  | .remainder => rho β / 2 + (W β (depth β)-chiR β) / 4

def rowEnergyDegree (β : ℝ) (i : MasterRow) := 1/4-rho β/2 + rowDamping β i

theorem row_exponents_lt_one {β : ℝ} (hβ : 0 < β) (hsmall : β ≤ 4/25)
    (i : MasterRow) : rowExponent β i < 1 := by
  have had := admissible_parameters β hβ hsmall
  cases i
  · exact had.2.2.2.2.2.1
  · exact lt_of_lt_of_le had.2.2.2.2.2.2.2.1 (min_le_left _ _)
  · exact lt_trans had.2.2.2.2.2.2.2.2.2 (by linarith : β<1)

theorem row_rates_exceed_target {β : ℝ} (hβ : 0 < β) (hsmall : β ≤ 4/25)
    (i : MasterRow) : (5/4:ℝ) < rowEnergyDegree β i / (1-rowExponent β i) := by
  have hr := all_rates_exceed_target β hβ hsmall
  have he (a z : ℝ) : a / (1-z) = (2*a/(1-z))/2 := by ring
  rw [he]
  have hdouble : (5/2:ℝ) < 2*rowEnergyDegree β i / (1-rowExponent β i) := by
    cases i
    · change (5/2:ℝ) < (2*(1/4-rho β/2+0)) / (1-alpha β)
      rw [show 2*(1/4-rho β/2+0) = 1/2-rho β by ring]
      exact hr.1
    · change (5/2:ℝ) < (2*(1/4-rho β/2+qNative β 2/4)) / (1-chi β)
      rw [show 2*(1/4-rho β/2+qNative β 2/4) = 1/2-rho β+2*(1/4)*qNative β 2 by ring]
      exact hr.2.1
    · change (5/2:ℝ) < (2*(1/4-rho β/2+(rho β/2+(W β (depth β)-chiR β)/4))) / (1-chiR β)
      rw [show 2*(1/4-rho β/2+(rho β/2+(W β (depth β)-chiR β)/4)) =
        1/2+2*(1/4)*(W β (depth β)-chiR β) by ring]
      exact hr.2.2
  linarith

def lossyRows (β Λ m : ℝ) (δ η : MasterRow → ℝ) :=
  ∑ i : MasterRow, Λ ^ (-rowDamping β i + δ i) * m ^ (rowExponent β i-η i)

def LossyFullMaster (β C Λ K m err : ℝ) (d : ℕ) (δ η : MasterRow → ℝ) : Prop :=
  K ≤ C * (linearK β d Λ * K + linearM β (depth β) Λ * m + lossyRows β Λ m δ η) + err

theorem scaled_lossyRows {β Λ m : ℝ} (δ η : MasterRow → ℝ) (hΛ : 0 < Λ) :
    energyScale β Λ * lossyRows β Λ m δ η =
      ∑ i : MasterRow, Λ ^ (-(rowEnergyDegree β i-δ i)) * m ^ (rowExponent β i-η i) := by
  unfold lossyRows energyScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, ← Real.rpow_add hΛ]
  have he : rho β/2-1/4+(-rowDamping β i+δ i) = -(rowEnergyDegree β i-δ i) := by
    unfold rowEnergyDegree
    ring
  rw [he]

def lossyMasterConstant (β C : ℝ) :=
  (∑ i : MasterRow, max 1
    ((((Finset.univ : Finset MasterRow).card+1:ℝ) * (2*C^2)) ^ (1/(1-rowExponent β i)))) +
      ((Finset.univ : Finset MasterRow).card+1:ℝ) * (2*C)

/-- The complete finite master still closes with simultaneous small
losses in all damping powers and all three nonlinear state exponents.
The tolerance is chosen after the fixed parameters, uniformly in the
actual losses, damping, and energy. -/
theorem lossy_full_master_decay {β C : ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 4/25) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : MasterRow → ℝ) (Λ K m err : ℝ) (d : ℕ),
      (∀ i, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      1 ≤ Λ → 0 ≤ K → 0 ≤ m →
      m ≤ C * energyScale β Λ * K →
      C * linearK β d Λ + C^2 * energyScale β Λ * linearM β (depth β) Λ ≤ 1/2 →
      err ≤ Λ ^ (-(2:ℝ)) → LossyFullMaster β C Λ K m err d δ η →
      m ≤ lossyMasterConstant β C * Λ ^ (-(5/4:ℝ)) := by
  obtain ⟨ε,hε,hclose⟩ := finite_lossy_ledger_closes (Finset.univ : Finset MasterRow)
    (a:=rowEnergyDegree β) (z:=rowExponent β) (C:=fun _ => 2*C^2) (E:=2*C)
    (by norm_num : (0:ℝ)≤5/4) (by positivity)
    (by intro i hi; positivity)
    (fun i _ => row_exponents_lt_one hβ hβsmall i)
    (fun i _ => row_rates_exceed_target hβ hβsmall i)
  refine ⟨ε,hε,?_⟩
  intro δ η Λ K m err d hl hΛ hK hm henergy hsmall herr hmaster
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hs : 0 ≤ energyScale β Λ := Real.rpow_nonneg hΛpos.le _
  have hs1 : energyScale β Λ ≤ 1 := by
    have hρ := (admissible_parameters β hβ hβsmall).2.1
    exact Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith)
  have hb : 0 ≤ C * linearM β (depth β) Λ := mul_nonneg hC (linearM_nonneg _ hΛpos.le)
  have hK' : K ≤ (C * linearK β d Λ) * K + (C * linearM β (depth β) Λ) * m +
      (C * lossyRows β Λ m δ η + err) := by
    simpa only [LossyFullMaster, mul_add, mul_assoc, add_assoc] using hmaster
  have hsmall' : C * linearK β d Λ + (C * linearM β (depth β) Λ) * (C * energyScale β Λ) ≤ 1/2 := by
    nlinarith only [hsmall]
  have hKb := absorb_two_linear_slots hK' henergy hb hsmall' hK
  have hab : m ≤ 2*C^2 * (energyScale β Λ * lossyRows β Λ m δ η) + 2*C*energyScale β Λ*err := by
    have hh := mul_le_mul_of_nonneg_left hKb (mul_nonneg hC hs)
    nlinarith only [hh,henergy]
  have htail : 2*C*energyScale β Λ*err ≤ 2*C*Λ ^ (-(2:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left herr (by positivity : 0≤2*C*energyScale β Λ)
    have hh' := mul_le_mul_of_nonneg_left hs1 (by positivity : 0≤2*C*Λ ^ (-(2:ℝ)))
    nlinarith only [hh,hh']
  rw [scaled_lossyRows δ η hΛpos, Finset.mul_sum] at hab
  have hrow : m ≤ ∑ i : MasterRow, (2*C^2) * Λ ^ (-(rowEnergyDegree β i-δ i)) * m ^ (rowExponent β i-η i) +
      2*C*Λ ^ (-(2:ℝ)) := by
    simp only [mul_assoc] at hab ⊢
    linarith only [hab,htail]
  have he : 2*C*Λ ^ (-(2:ℝ)) ≤ 2*C*Λ ^ (-(5/4:ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hΛ (by norm_num)) (by positivity)
  exact hclose δ η m Λ (2*C*Λ ^ (-(2:ℝ))) (fun i _ => hl i) hm hΛ he hrow

/-- After the small losses are fixed, the full lossy master also makes
the actual damping cost vanish. Linear-coefficient absorption follows
from the proved limits rather than a further hypothesis. -/
theorem lossy_full_master_cost_limit {β C : ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 4/25) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : MasterRow → ℝ) (K m err : ℝ → ℝ) (d : ℕ),
      (∀ i, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      (∀ᶠ Λ in atTop, 0 ≤ K Λ ∧ 0 ≤ m Λ ∧
        m Λ ≤ C * energyScale β Λ * K Λ ∧ err Λ ≤ Λ ^ (-(2:ℝ)) ∧
        LossyFullMaster β C Λ (K Λ) (m Λ) (err Λ) d δ η) →
      Tendsto (fun Λ => Λ ^ (2:ℕ) * m Λ ^ (2:ℕ)) atTop (𝓝 0) := by
  obtain ⟨ε,hε,hclose⟩ := lossy_full_master_decay hβ hβsmall hC
  refine ⟨ε,hε,?_⟩
  intro δ η K m err d hl hfull
  have hsmall := (full_linear_coefficient_tends_zero (C:=C) hβ hβsmall (depth β) d).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  apply damping_cost_tends_to_zero (p:=(5/2:ℝ)) (C:=lossyMasterConstant β C ^ (2:ℕ)) (by norm_num)
  filter_upwards [hfull,hsmall,eventually_ge_atTop (1:ℝ)] with Λ hΛ hs hΛ1
  have hm := hclose δ η Λ (K Λ) (m Λ) (err Λ) d hl hΛ1 hΛ.1 hΛ.2.1 hΛ.2.2.1
    hs.le hΛ.2.2.2.1 hΛ.2.2.2.2
  refine ⟨sq_nonneg _, ?_⟩
  have hp := pow_le_pow_left₀ hΛ.2.1 hm 2
  have hΛ0 : 0 ≤ Λ := by linarith
  calc
    _ ≤ (lossyMasterConstant β C * Λ ^ (-(5/4:ℝ))) ^ (2:ℕ) := hp
    _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hΛ0]; norm_num

end SHE
