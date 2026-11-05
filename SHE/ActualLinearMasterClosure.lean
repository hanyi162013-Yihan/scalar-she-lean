module
public import SHE.ZeroNativeDyadicMaster
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace SHE.ActualLinearMasterClosure
open Filter Topology ZeroNativeDyadicMaster

/-- Conditional deterministic comparison ledger with the actual linear
coefficients supplied by the estimates, including small power losses.
It is not a theorem asserting the stochastic comparison inequality. -/
def Bound(β C Λ K m err a b:ℝ)(δ η:MasterRow→ℝ):Prop:=
  K≤C*(a*K+b*m+ZeroNativeDyadicMaster.rows β Λ m δ η)+err

theorem decay {β C : ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 4/25) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : MasterRow → ℝ) (Λ K m err a b : ℝ),
      (∀ i, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      1 ≤ Λ → 0 ≤ K → 0 ≤ m →
      m ≤ C * energyScale β Λ * K → 0≤b →
      C * a + C^2 * energyScale β Λ * b ≤ 1/2 →
      err ≤ Λ ^ (-(2:ℝ)) → Bound β C Λ K m err a b δ η →
      m ≤ ZeroNativeDyadicMaster.constant β C * Λ ^ (-(5/4:ℝ)) := by
  obtain ⟨ε,hε,hclose⟩ := finite_lossy_ledger_closes (Finset.univ : Finset MasterRow)
    (a:=ZeroNativeDyadicMaster.rowEnergyDegree β) (z:=rowExponent β) (C:=fun _ => 2*C^2) (E:=2*C)
    (by norm_num : (0:ℝ)≤5/4) (by positivity)
    (by intro i hi; positivity)
    (fun i _ => ZeroNativeDyadicMaster.row_exponents_lt_one hβ hβsmall i)
    (fun i _ => ZeroNativeDyadicMaster.row_rates_exceed_target hβ hβsmall i)
  refine ⟨ε,hε,?_⟩
  intro δ η Λ K m err a b hl hΛ hK hm henergy hb0 hsmall herr hmaster
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hs : 0 ≤ energyScale β Λ := Real.rpow_nonneg hΛpos.le _
  have hs1 : energyScale β Λ ≤ 1 := by
    have hρ := (admissible_parameters β hβ hβsmall).2.1
    exact Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith)
  have hb : 0 ≤ C * b := mul_nonneg hC hb0
  have hK' : K ≤ (C * a) * K + (C * b) * m +
      (C * ZeroNativeDyadicMaster.rows β Λ m δ η + err) := by
    simpa only [Bound, mul_add, mul_assoc, add_assoc] using hmaster
  have hsmall' : C * a + (C * b) * (C * energyScale β Λ) ≤ 1/2 := by
    nlinarith only [hsmall]
  have hKb := absorb_two_linear_slots hK' henergy hb hsmall' hK
  have hab : m ≤ 2*C^2 * (energyScale β Λ * ZeroNativeDyadicMaster.rows β Λ m δ η) + 2*C*energyScale β Λ*err := by
    have hh := mul_le_mul_of_nonneg_left hKb (mul_nonneg hC hs)
    nlinarith only [hh,henergy]
  have htail : 2*C*energyScale β Λ*err ≤ 2*C*Λ ^ (-(2:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left herr (by positivity : 0≤2*C*energyScale β Λ)
    have hh' := mul_le_mul_of_nonneg_left hs1 (by positivity : 0≤2*C*Λ ^ (-(2:ℝ)))
    nlinarith only [hh,hh']
  rw [ZeroNativeDyadicMaster.scaled_rows δ η hΛpos, Finset.mul_sum] at hab
  have hrow : m ≤ ∑ i : MasterRow, (2*C^2) * Λ ^ (-(ZeroNativeDyadicMaster.rowEnergyDegree β i-δ i)) * m ^ (rowExponent β i-η i) +
      2*C*Λ ^ (-(2:ℝ)) := by
    simp only [mul_assoc] at hab ⊢
    linarith only [hab,htail]
  have he : 2*C*Λ ^ (-(2:ℝ)) ≤ 2*C*Λ ^ (-(5/4:ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hΛ (by norm_num)) (by positivity)
  exact hclose δ η m Λ (2*C*Λ ^ (-(2:ℝ))) (fun i _ => hl i) hm hΛ he hrow


/-- The actual linear coefficient need only tend to zero after the
proved energy scaling; no particular unperturbed polynomial rate is
required. The analytic comparison remains an explicit premise. -/
theorem cost_limit {β C : ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 4/25) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : MasterRow → ℝ) (K m err a b : ℝ → ℝ),
      (∀ i, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      Tendsto (fun Λ=>C*a Λ+C^2*energyScale β Λ*b Λ) atTop (𝓝 (0:ℝ)) →
      (∀ᶠ Λ in atTop,0≤b Λ) →
      (∀ᶠ Λ in atTop, 0 ≤ K Λ ∧ 0 ≤ m Λ ∧
        m Λ ≤ C * energyScale β Λ * K Λ ∧ err Λ ≤ Λ ^ (-(2:ℝ)) ∧
        Bound β C Λ (K Λ) (m Λ) (err Λ) (a Λ) (b Λ) δ η) →
      Tendsto (fun Λ => Λ ^ (2:ℕ) * m Λ ^ (2:ℕ)) atTop (𝓝 0) := by
  obtain ⟨ε,hε,hclose⟩ := decay hβ hβsmall hC
  refine ⟨ε,hε,?_⟩
  intro δ η K m err a b hl hcoeff hbfull hfull
  have hsmall := hcoeff.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  apply damping_cost_tends_to_zero (p:=(5/2:ℝ)) (C:=ZeroNativeDyadicMaster.constant β C ^ (2:ℕ)) (by norm_num)
  filter_upwards [hfull,hsmall,eventually_ge_atTop (1:ℝ),hbfull] with Λ hΛ hs hΛ1 hb
  have hm := hclose δ η Λ (K Λ) (m Λ) (err Λ) (a Λ) (b Λ) hl hΛ1 hΛ.1 hΛ.2.1 hΛ.2.2.1 hb
    hs.le hΛ.2.2.2.1 hΛ.2.2.2.2
  refine ⟨sq_nonneg _, ?_⟩
  have hp := pow_le_pow_left₀ hΛ.2.1 hm 2
  have hΛ0 : 0 ≤ Λ := by linarith
  calc
    _ ≤ (ZeroNativeDyadicMaster.constant β C * Λ ^ (-(5/4:ℝ))) ^ (2:ℕ) := hp
    _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hΛ0]; norm_num
end SHE.ActualLinearMasterClosure
