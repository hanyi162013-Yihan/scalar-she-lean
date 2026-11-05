module

public import SHE.Feedback

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open Filter Topology

/-- The finite master ledger has one nonlinear slot per retained row
and one independent deterministic-error slot. -/
theorem finite_slots {I : Type*} (s : Finset I) {x e : ℝ} {a : I → ℝ}
    (h : x ≤ ∑ i ∈ s, a i + e) :
    (∃ i ∈ s, x ≤ (s.card + 1 : ℝ) * a i) ∨ x ≤ (s.card + 1 : ℝ) * e := by
  classical
  by_contra hn
  push Not at hn
  have hs : (s.card + 1 : ℝ) * ∑ i ∈ s, a i ≤ (s.card : ℝ) * x := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _i ∈ s, x := Finset.sum_le_sum (fun i hi => (hn.1 i hi).le)
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (s.card + 1 : ℝ))
  nlinarith [hn.2]

/-- Quantitative decay from any fixed finite ledger. Every row and its
strictly sublinear state exponent is retained explicitly. -/
theorem finite_row_decay {I : Type*} (s : Finset I)
    {x Λ target e E : ℝ} {C a z : I → ℝ}
    (hx : 0 ≤ x) (hΛ : 1 ≤ Λ) (hE : 0 ≤ E)
    (hC : ∀ i ∈ s, 0 ≤ C i) (hz : ∀ i ∈ s, z i < 1)
    (hrate : ∀ i ∈ s, target ≤ a i / (1-z i))
    (he : e ≤ E * Λ ^ (-target))
    (h : x ≤ ∑ i ∈ s, C i * Λ ^ (-a i) * x ^ z i + e) :
    x ≤ ((∑ i ∈ s, ((s.card + 1 : ℝ) * C i) ^ (1 / (1-z i))) +
      (s.card + 1 : ℝ) * E) * Λ ^ (-target) := by
  classical
  let B : I → ℝ := fun i => ((s.card + 1 : ℝ) * C i) ^ (1 / (1-z i))
  have hB : ∀ i ∈ s, 0 ≤ B i := fun i hi =>
    Real.rpow_nonneg (mul_nonneg (by positivity) (hC i hi)) _
  have hsum : 0 ≤ ∑ i ∈ s, B i := Finset.sum_nonneg hB
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  rcases finite_slots s h with hrow | herr
  · obtain ⟨i,hi,hbound⟩ := hrow
    have hx' : x ≤ (((s.card + 1 : ℝ) * C i) * Λ ^ (-a i)) * x ^ z i := by
      nlinarith only [hbound]
    have hb := sublinear_decay hx (mul_nonneg (by positivity) (hC i hi))
      hΛpos (hz i hi) hx'
    have hpow : Λ ^ (-a i / (1-z i)) ≤ Λ ^ (-target) :=
      Real.rpow_le_rpow_of_exponent_le hΛ (by rw [neg_div]; linarith [hrate i hi])
    have hBi : B i ≤ ∑ j ∈ s, B j := Finset.single_le_sum hB hi
    change x ≤ ((∑ i ∈ s, B i) + (s.card + 1 : ℝ) * E) * Λ ^ (-target)
    calc
      _ ≤ B i * Λ ^ (-a i / (1-z i)) := hb
      _ ≤ B i * Λ ^ (-target) := mul_le_mul_of_nonneg_left hpow (hB i hi)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [hBi]) (Real.rpow_nonneg hΛpos.le _)
  · change x ≤ ((∑ i ∈ s, B i) + (s.card + 1 : ℝ) * E) * Λ ^ (-target)
    have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (s.card + 1 : ℝ))
    have hn := mul_nonneg hsum (Real.rpow_nonneg hΛpos.le (-target))
    nlinarith only [herr, hh, hn]

/-- One common tolerance works for all finitely many numerator and
state-power losses, after fixing the finite depth and strict margins. -/
theorem finite_joint_rate_losses_stable {I : Type*} (s : Finset I)
    {a z : I → ℝ} {target : ℝ} (htarget : 0 ≤ target)
    (hz : ∀ i ∈ s, z i < 1) (hrate : ∀ i ∈ s, target < a i / (1-z i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ∀ δ η : ℝ,
      0 ≤ δ → δ ≤ ε → 0 ≤ η → η ≤ ε → target < (a i-δ) / (1-(z i-η)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨εs,hεs,hs⟩ := ih (fun j hj => hz j (Finset.mem_insert_of_mem hj))
      (fun j hj => hrate j (Finset.mem_insert_of_mem hj))
    obtain ⟨εi,hεi,hri⟩ := joint_rate_losses_stable (hz i (Finset.mem_insert_self _ _))
      htarget (hrate i (Finset.mem_insert_self _ _))
    refine ⟨min εi εs, lt_min hεi hεs, ?_⟩
    intro j hj δ η hδ hδε hη hηε
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hri δ η hδ (hδε.trans (min_le_left _ _)) hη (hηε.trans (min_le_left _ _))
    · exact hs j hj δ η hδ (hδε.trans (min_le_right _ _)) hη (hηε.trans (min_le_right _ _))

theorem loss_constant_le {A z η : ℝ} (hA : 0 ≤ A) (hz : z < 1) (hη : 0 ≤ η) :
    A ^ (1 / (1-(z-η))) ≤ max 1 (A ^ (1 / (1-z))) := by
  have hp : 0 < 1-z := by linarith
  have hp' : 0 < 1-(z-η) := by linarith
  by_cases hA1 : 1 ≤ A
  · apply le_trans _ (le_max_right _ _)
    apply Real.rpow_le_rpow_of_exponent_le hA1
    exact one_div_le_one_div_of_le hp (by linarith)
  · apply le_trans _ (le_max_left _ _)
    exact Real.rpow_le_one hA (le_of_lt (lt_of_not_ge hA1)) (by positivity)

/-- A finite lossy ledger closes uniformly in all permitted small losses.
This makes the manuscript's 'choose losses after the strict margins'
step a checked theorem with an explicit uniform constant. -/
theorem finite_lossy_ledger_closes {I : Type*} (s : Finset I)
    {a z C : I → ℝ} {target E : ℝ} (htarget : 0 ≤ target) (hE : 0 ≤ E)
    (hC : ∀ i ∈ s, 0 ≤ C i) (hz : ∀ i ∈ s, z i < 1)
    (hrate : ∀ i ∈ s, target < a i / (1-z i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : I → ℝ) (x Λ e : ℝ),
      (∀ i ∈ s, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      0 ≤ x → 1 ≤ Λ → e ≤ E * Λ ^ (-target) →
      x ≤ ∑ i ∈ s, C i * Λ ^ (-(a i-δ i)) * x ^ (z i-η i) + e →
      x ≤ ((∑ i ∈ s, max 1 (((s.card + 1 : ℝ) * C i) ^ (1 / (1-z i)))) +
        (s.card + 1 : ℝ) * E) * Λ ^ (-target) := by
  obtain ⟨ε,hε,hr⟩ := finite_joint_rate_losses_stable s htarget hz hrate
  refine ⟨ε,hε,?_⟩
  intro δ η x Λ e hl hx hΛ he hm
  have hb := finite_row_decay s hx hΛ hE hC
    (fun i hi => by have hh := hl i hi; linarith [hz i hi])
    (fun i hi => (hr i hi (δ i) (η i) (hl i hi).1 (hl i hi).2.1
      (hl i hi).2.2.1 (hl i hi).2.2.2).le) he hm
  have hconst : (∑ i ∈ s, ((s.card + 1 : ℝ) * C i) ^ (1 / (1-(z i-η i)))) ≤
      ∑ i ∈ s, max 1 (((s.card + 1 : ℝ) * C i) ^ (1 / (1-z i))) := by
    exact Finset.sum_le_sum fun i hi => loss_constant_le
      (mul_nonneg (by positivity) (hC i hi)) (hz i hi) (hl i hi).2.2.1
  exact hb.trans (mul_le_mul_of_nonneg_right (add_le_add hconst le_rfl)
    (Real.rpow_nonneg (by linarith : 0 ≤ Λ) _))

end SHE
