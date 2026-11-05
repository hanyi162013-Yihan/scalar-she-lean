module

public import SHE.LossyMaster
public import SHE.DyadicMasterRemainder

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.ZeroNativeDyadicMaster
open Filter Topology

/-! Deterministic closure for the ACTUALLY proved retained-output
remainder coefficient Lambda^(-rho/2-1) and a native row with NO
additional damping gain. This weaker native estimate still closes the
actual final damping cost. No implication from a conditional analytic
master premise to an actual stochastic comparison is asserted here. -/

def rowDamping (β : ℝ) : MasterRow → ℝ
  | .gaussian => 0
  | .native => 0
  | .remainder => rho β / 2 + 1

def rowEnergyDegree (β : ℝ) (i : MasterRow) := 1/4-rho β/2 + rowDamping β i

theorem row_exponents_lt_one {β : ℝ} (hβ : 0 < β) (hsmall : β ≤ 4/25)
    (i : MasterRow) : rowExponent β i < 1 := by
  have had := admissible_parameters β hβ hsmall
  cases i
  · exact had.2.2.2.2.2.1
  · exact lt_of_lt_of_le had.2.2.2.2.2.2.2.1 (min_le_left _ _)
  · exact lt_trans had.2.2.2.2.2.2.2.2.2 (by linarith : β<1)

/-- The coarser R^-8 actual tail still leaves a strict target-rate
margin: its scaled remainder degree is exactly5/4, divided by1-beta/2. -/
theorem row_rates_exceed_target {β:ℝ} (hβ:0<β) (hsmall:β≤4/25)
    (i:MasterRow):(5/4:ℝ)<rowEnergyDegree β i/(1-rowExponent β i):=by
  cases i
  · simpa only [rowEnergyDegree,rowDamping,SHE.rowEnergyDegree,SHE.rowDamping] using
      SHE.row_rates_exceed_target hβ hsmall MasterRow.gaussian
  · change (5/4:ℝ)<(1/4-rho β/2+0)/(1-chi β)
    have hz:0<1-chi β:=by dsimp [chi];linarith
    apply (lt_div_iff₀ hz).mpr
    dsimp [rho,chi]
    linarith
  · change (5/4:ℝ)<(1/4-rho β/2+(rho β/2+1))/(1-chiR β)
    have hz:0<1-chiR β:=by dsimp[chiR];linarith
    apply (lt_div_iff₀ hz).mpr
    dsimp[chiR]
    linarith

def rows (β Λ m : ℝ) (δ η : MasterRow → ℝ) :=
  ∑ i : MasterRow, Λ ^ (-rowDamping β i + δ i) * m ^ (rowExponent β i-η i)

def Bound (β C Λ K m err : ℝ) (d : ℕ) (δ η : MasterRow → ℝ) : Prop :=
  K ≤ C * (linearK β d Λ * K + linearM β (depth β) Λ * m + rows β Λ m δ η) + err

theorem scaled_rows {β Λ m : ℝ} (δ η : MasterRow → ℝ) (hΛ : 0 < Λ) :
    energyScale β Λ * rows β Λ m δ η =
      ∑ i : MasterRow, Λ ^ (-(rowEnergyDegree β i-δ i)) * m ^ (rowExponent β i-η i) := by
  unfold rows energyScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, ← Real.rpow_add hΛ]
  have he : rho β/2-1/4+(-rowDamping β i+δ i) = -(rowEnergyDegree β i-δ i) := by
    unfold rowEnergyDegree
    ring
  rw [he]

def constant (β C : ℝ) :=
  (∑ i : MasterRow, max 1
    ((((Finset.univ : Finset MasterRow).card+1:ℝ) * (2*C^2)) ^ (1/(1-rowExponent β i)))) +
      ((Finset.univ : Finset MasterRow).card+1:ℝ) * (2*C)

/-- The complete finite master still closes with simultaneous small
losses in all damping powers and all three nonlinear state exponents.
The tolerance is chosen after the fixed parameters, uniformly in the
actual losses, damping, and energy. -/
theorem decay {β C : ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 4/25) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : MasterRow → ℝ) (Λ K m err : ℝ) (d : ℕ),
      (∀ i, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      1 ≤ Λ → 0 ≤ K → 0 ≤ m →
      m ≤ C * energyScale β Λ * K →
      C * linearK β d Λ + C^2 * energyScale β Λ * linearM β (depth β) Λ ≤ 1/2 →
      err ≤ Λ ^ (-(2:ℝ)) → Bound β C Λ K m err d δ η →
      m ≤ constant β C * Λ ^ (-(5/4:ℝ)) := by
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
      (C * rows β Λ m δ η + err) := by
    simpa only [Bound, mul_add, mul_assoc, add_assoc] using hmaster
  have hsmall' : C * linearK β d Λ + (C * linearM β (depth β) Λ) * (C * energyScale β Λ) ≤ 1/2 := by
    nlinarith only [hsmall]
  have hKb := absorb_two_linear_slots hK' henergy hb hsmall' hK
  have hab : m ≤ 2*C^2 * (energyScale β Λ * rows β Λ m δ η) + 2*C*energyScale β Λ*err := by
    have hh := mul_le_mul_of_nonneg_left hKb (mul_nonneg hC hs)
    nlinarith only [hh,henergy]
  have htail : 2*C*energyScale β Λ*err ≤ 2*C*Λ ^ (-(2:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left herr (by positivity : 0≤2*C*energyScale β Λ)
    have hh' := mul_le_mul_of_nonneg_left hs1 (by positivity : 0≤2*C*Λ ^ (-(2:ℝ)))
    nlinarith only [hh,hh']
  rw [scaled_rows δ η hΛpos, Finset.mul_sum] at hab
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
theorem cost_limit {β C : ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 4/25) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : MasterRow → ℝ) (K m err : ℝ → ℝ) (d : ℕ),
      (∀ i, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      (∀ᶠ Λ in atTop, 0 ≤ K Λ ∧ 0 ≤ m Λ ∧
        m Λ ≤ C * energyScale β Λ * K Λ ∧ err Λ ≤ Λ ^ (-(2:ℝ)) ∧
        Bound β C Λ (K Λ) (m Λ) (err Λ) d δ η) →
      Tendsto (fun Λ => Λ ^ (2:ℕ) * m Λ ^ (2:ℕ)) atTop (𝓝 0) := by
  obtain ⟨ε,hε,hclose⟩ := decay hβ hβsmall hC
  refine ⟨ε,hε,?_⟩
  intro δ η K m err d hl hfull
  have hsmall := (full_linear_coefficient_tends_zero (C:=C) hβ hβsmall (depth β) d).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  apply damping_cost_tends_to_zero (p:=(5/2:ℝ)) (C:=constant β C ^ (2:ℕ)) (by norm_num)
  filter_upwards [hfull,hsmall,eventually_ge_atTop (1:ℝ)] with Λ hΛ hs hΛ1
  have hm := hclose δ η Λ (K Λ) (m Λ) (err Λ) d hl hΛ1 hΛ.1 hΛ.2.1 hΛ.2.2.1
    hs.le hΛ.2.2.2.1 hΛ.2.2.2.2
  refine ⟨sq_nonneg _, ?_⟩
  have hp := pow_le_pow_left₀ hΛ.2.1 hm 2
  have hΛ0 : 0 ≤ Λ := by linarith
  calc
    _ ≤ (constant β C * Λ ^ (-(5/4:ℝ))) ^ (2:ℕ) := hp
    _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hΛ0]; norm_num


end SHE.ZeroNativeDyadicMaster
