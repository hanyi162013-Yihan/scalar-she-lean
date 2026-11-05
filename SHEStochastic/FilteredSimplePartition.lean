/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Adapted from SimpleProcessPartition.lean, formal-mathfin commit
3c41aee9bf2d9743f9e66b439f90d1635843d2d2. The deterministic partition and
cell proofs are reused for arbitrary filtrations and Banach-valued steps.
No Brownian law, Girsanov or natural-filtration premise is needed here.
-/
module

public import SHEStochastic.FilteredItoL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.FilteredSimplePartition
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The finite set of cell boundaries of a simple process on `[0,T]`: `0`, `T`, and every endpoint
of every interval in the `value` support. -/
noncomputable def marshalEndpoints (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) : Finset ℝ≥0 :=
  insert 0 (insert T (V.value.support.image Prod.fst ∪ V.value.support.image Prod.snd))

/-- `0` is always a cell boundary. -/
lemma zero_mem_marshalEndpoints (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) :
    (0 : ℝ≥0) ∈ marshalEndpoints 𝓖 T V := Finset.mem_insert_self _ _

/-- `T` is always a cell boundary. -/
lemma T_mem_marshalEndpoints (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) :
    T ∈ marshalEndpoints 𝓖 T V :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- The endpoint set is nonempty (it contains `0`). -/
lemma marshalEndpoints_nonempty (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) :
    (marshalEndpoints 𝓖 T V).Nonempty :=
  ⟨0, zero_mem_marshalEndpoints 𝓖 T V⟩

/-- **Every cell boundary is `≤ T`.** `0 ≤ T`; `T ≤ T`; a left endpoint `p.1 ≤ p.2 ≤ T`; a right
endpoint `p.2 ≤ T` — the last two using the clamp hypothesis `hle` and `V.le_of_mem_support_value`. -/
lemma marshalEndpoints_le_T (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖)
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    ∀ x ∈ marshalEndpoints 𝓖 T V, x ≤ T := by
  intro x hx
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with rfl | rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact zero_le
  · exact le_refl _
  · exact (V.le_of_mem_support_value p hp).trans (hle p hp)
  · exact hle p hp

/-- The monotone partition read off the sorted endpoint set: the `i`-th smallest boundary for
`i < card`, clamped to `T` beyond. This is the `s : ℕ → ℝ≥0` fed to `isExpQMartingale_BthetaSimple`. -/
noncomputable def marshalPart (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (i : ℕ) : ℝ≥0 :=
  if h : i < (marshalEndpoints 𝓖 T V).card then
    (marshalEndpoints 𝓖 T V).orderEmbOfFin rfl ⟨i, h⟩
  else T

/-- `marshalPart` is monotone: within the enumerated range by `orderEmbOfFin`'s monotonicity, and
constant `= T` beyond (`T` is the maximum, since every interval endpoint is `≤ T` after clamping and
`T` itself is a boundary). -/
lemma marshalPart_mono (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖)
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    Monotone (marshalPart 𝓖 T V) := by
  have hE := marshalEndpoints_le_T 𝓖 T V hle
  intro i j hij
  unfold marshalPart
  split_ifs with hi hj hj
  · exact ((marshalEndpoints 𝓖 T V).orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr hij)
  · exact hE _ (Finset.orderEmbOfFin_mem _ _ _)
  · omega
  · exact le_refl _

/-- The per-cell multiplier: on cell `(marshalPart i, marshalPart (i+1)]`, the sum of the values of
every interval in `V.value` that **covers** the cell (`p.1 ≤ sᵢ` and `sᵢ₊₁ ≤ p.2`). This is the
`c : ℕ → Ω → ℝ` fed to `isExpQMartingale_BthetaSimple`. The covering test is deterministic (no `ω`),
so measurability/boundedness reduce to those of the finitely many covering values. -/
noncomputable def marshalMult (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (i : ℕ) (ω : Ω) : E :=
  ∑ p ∈ V.value.support,
    (if p.1 ≤ marshalPart 𝓖 T V i ∧ marshalPart 𝓖 T V (i + 1) ≤ p.2
      then V.value p ω else 0)

/-- **The multiplier is adapted at the cell's left endpoint.** Each covering value `V.value p` is
`𝓕_{p.1}`-measurable, and covering forces `p.1 ≤ sᵢ`, so it is `𝓕_{sᵢ}`-measurable; the finite sum
stays `𝓕_{sᵢ}`-measurable. This is the `hc` hypothesis of `isExpQMartingale_BthetaSimple`. -/
lemma stronglyMeasurable_marshalMult (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (i : ℕ) :
    StronglyMeasurable[(𝓖 (marshalPart 𝓖 T V i) : MeasurableSpace Ω)]
      (marshalMult 𝓖 T V i) := by
  unfold marshalMult
  refine Finset.stronglyMeasurable_fun_sum _ (fun p _ ↦ ?_)
  by_cases hcond : p.1 ≤ marshalPart 𝓖 T V i ∧ marshalPart 𝓖 T V (i + 1) ≤ p.2
  · simp only [hcond]
    exact ((V.measurable_value p).mono (𝓖.mono hcond.1)
      le_rfl).stronglyMeasurable
  · simp only [hcond]
    exact stronglyMeasurable_const

/-- Consecutive enumerated cells are strictly increasing (`orderEmbOfFin` is strictly monotone). -/
lemma marshalPart_lt (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) {i : ℕ}
    (hi : i + 1 < (marshalEndpoints 𝓖 T V).card) :
    marshalPart 𝓖 T V i < marshalPart 𝓖 T V (i + 1) := by
  have hi' : i < (marshalEndpoints 𝓖 T V).card := by omega
  rw [marshalPart, dif_pos hi', marshalPart, dif_pos hi]
  exact ((marshalEndpoints 𝓖 T V).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega))

/-- **Consecutiveness.** Within an enumerated cell `(sᵢ, sᵢ₊₁]` there is no other boundary: every
endpoint is `≤ sᵢ` or `≥ sᵢ₊₁`. Since `orderEmbOfFin` enumerates *all* of `marshalEndpoints` in
order, any endpoint is some `marshalPart k`, and `k ≤ i` or `i+1 ≤ k`. -/
lemma marshalEndpoints_consecutive (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖)
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) {i : ℕ}
    {x : ℝ≥0} (hx : x ∈ marshalEndpoints 𝓖 T V) :
    x ≤ marshalPart 𝓖 T V i ∨ marshalPart 𝓖 T V (i + 1) ≤ x := by
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (marshalEndpoints 𝓖 T V) rfl] at hx
  obtain ⟨k, hk⟩ := hx
  have hxk : marshalPart 𝓖 T V k.val = x := by
    rw [marshalPart, dif_pos k.isLt]; exact hk
  rcases le_or_gt k.val i with h | h
  · exact Or.inl (hxk ▸ marshalPart_mono 𝓖 T V hle h)
  · exact Or.inr (hxk ▸ marshalPart_mono 𝓖 T V hle h)

/-- Every left endpoint of a support interval is a cell boundary. -/
lemma fst_mem_marshalEndpoints (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) {p : ℝ≥0 × ℝ≥0}
    (hp : p ∈ V.value.support) : p.1 ∈ marshalEndpoints 𝓖 T V := by
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))

/-- Every right endpoint of a support interval is a cell boundary. -/
lemma snd_mem_marshalEndpoints (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) {p : ℝ≥0 × ℝ≥0}
    (hp : p ∈ V.value.support) : p.2 ∈ marshalEndpoints 𝓖 T V := by
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inr ⟨p, hp, rfl⟩))

/-- **Cell membership ↔ covering.** For a point `t` in the enumerated cell `(sᵢ, sᵢ₊₁]`, and an
interval `(p.1, p.2]` of the support, `t ∈ (p.1, p.2]` exactly when the interval covers the whole
cell (`p.1 ≤ sᵢ` and `sᵢ₊₁ ≤ p.2`). The `←` is monotonicity; the `→` uses consecutiveness (no
boundary strictly inside the cell) applied to the endpoints `p.1`, `p.2`. -/
lemma mem_Ioc_iff_cover (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {i : ℕ} {t : ℝ≥0} (ht1 : marshalPart 𝓖 T V i < t)
    (ht2 : t ≤ marshalPart 𝓖 T V (i + 1)) {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.value.support) :
    t ∈ Set.Ioc p.1 p.2 ↔
      (p.1 ≤ marshalPart 𝓖 T V i ∧ marshalPart 𝓖 T V (i + 1) ≤ p.2) := by
  constructor
  · rintro ⟨htp1, htp2⟩
    refine ⟨?_, ?_⟩
    · rcases marshalEndpoints_consecutive 𝓖 T V hle (i := i)
        (fst_mem_marshalEndpoints 𝓖 T V hp) with h | h
      · exact h
      · exact absurd ((h.trans_lt htp1).trans_le ht2) (lt_irrefl _)
    · rcases marshalEndpoints_consecutive 𝓖 T V hle (i := i)
        (snd_mem_marshalEndpoints 𝓖 T V hp) with h | h
      · exact absurd (h.trans_lt (ht1.trans_le htp2)) (lt_irrefl _)
      · exact h
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans_lt ht1, ht2.trans h2⟩

/-- On the enumerated range the partition is order-reflecting: `sₐ ≤ sᵢ ↔ a ≤ i`. -/
lemma marshalPart_le_iff (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) {a i : ℕ}
    (ha : a < (marshalEndpoints 𝓖 T V).card) (hi : i < (marshalEndpoints 𝓖 T V).card) :
    marshalPart 𝓖 T V a ≤ marshalPart 𝓖 T V i ↔ a ≤ i := by
  rw [marshalPart, dif_pos ha, marshalPart, dif_pos hi,
    ((marshalEndpoints 𝓖 T V).orderEmbOfFin rfl).le_iff_le]
  exact Fin.mk_le_mk

/-- Every cell boundary is realized: `x ∈ marshalEndpoints → x = marshalPart k` for some `k < card`. -/
lemma exists_marshalPart_eq (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) {x : ℝ≥0}
    (hx : x ∈ marshalEndpoints 𝓖 T V) :
    ∃ k, k < (marshalEndpoints 𝓖 T V).card ∧ marshalPart 𝓖 T V k = x := by
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (marshalEndpoints 𝓖 T V) rfl] at hx
  obtain ⟨k, hk⟩ := hx
  exact ⟨k.val, k.isLt, by rw [marshalPart, dif_pos k.isLt]; exact hk⟩

/-- **Telescoping over covering cells (general endpoint function `F`).** For a support interval
`(p.1, p.2]` (its endpoints are cell boundaries), summing `F(sᵢ₊₁) − F(sᵢ)` over exactly the cells
`i < N` the interval covers yields `F(p.2) − F(p.1)`: the covering cells are the block `Ico a b`
where `sₐ = p.1`, `s_b = p.2`, and the block telescopes. Instantiated with `F = B(·)ω` for the
stochastic exponent and `F = min · u` for the drift. -/
lemma telescope_cover (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖)
    {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.value.support) (F : ℝ≥0 → ℝ)
    {N : ℕ} (hN : N + 1 = (marshalEndpoints 𝓖 T V).card) :
    ∑ i ∈ Finset.range N,
      (if p.1 ≤ marshalPart 𝓖 T V i ∧ marshalPart 𝓖 T V (i + 1) ≤ p.2
        then F (marshalPart 𝓖 T V (i + 1)) - F (marshalPart 𝓖 T V i) else 0)
      = F p.2 - F p.1 := by
  obtain ⟨a, ha, ha_eq⟩ := exists_marshalPart_eq 𝓖 T V (fst_mem_marshalEndpoints 𝓖 T V hp)
  obtain ⟨b, hb, hb_eq⟩ := exists_marshalPart_eq 𝓖 T V (snd_mem_marshalEndpoints 𝓖 T V hp)
  have hab : a ≤ b := by
    rw [← marshalPart_le_iff 𝓖 T V ha hb, ha_eq, hb_eq]
    exact V.le_of_mem_support_value p hp
  rw [← ha_eq, ← hb_eq, ← Finset.sum_filter]
  have hset : ((Finset.range N).filter
      (fun i ↦ marshalPart 𝓖 T V a ≤ marshalPart 𝓖 T V i ∧
        marshalPart 𝓖 T V (i + 1) ≤ marshalPart 𝓖 T V b)) = Finset.Ico a b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hiN, hai, hib⟩
      have hi_card : i < (marshalEndpoints 𝓖 T V).card := by omega
      have hi1_card : i + 1 < (marshalEndpoints 𝓖 T V).card := by omega
      rw [marshalPart_le_iff 𝓖 T V ha hi_card] at hai
      rw [marshalPart_le_iff 𝓖 T V hi1_card hb] at hib
      exact ⟨hai, by omega⟩
    · rintro ⟨hai, hib⟩
      have hi_card : i < (marshalEndpoints 𝓖 T V).card := by omega
      have hi1_card : i + 1 < (marshalEndpoints 𝓖 T V).card := by omega
      refine ⟨by omega, ?_, ?_⟩
      · rw [marshalPart_le_iff 𝓖 T V ha hi_card]; exact hai
      · rw [marshalPart_le_iff 𝓖 T V hi1_card hb]; omega
  rw [hset, Finset.sum_Ico_eq_sub _ hab,
    Finset.sum_range_sub (fun i ↦ F (marshalPart 𝓖 T V i)) b,
    Finset.sum_range_sub (fun i ↦ F (marshalPart 𝓖 T V i)) a]
  ring

/-- The partition starts at `0` (the least boundary). -/
lemma marshalPart_zero (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    marshalPart 𝓖 T V 0 = 0 := by
  refine le_antisymm ?_ zero_le
  obtain ⟨k, _, hk⟩ := exists_marshalPart_eq 𝓖 T V (zero_mem_marshalEndpoints 𝓖 T V)
  calc marshalPart 𝓖 T V 0
      ≤ marshalPart 𝓖 T V k := marshalPart_mono 𝓖 T V hle (Nat.zero_le k)
    _ = 0 := hk

/-- Every partition point is `≤ T`. -/
lemma marshalPart_le_T (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    (i : ℕ) : marshalPart 𝓖 T V i ≤ T := by
  by_cases h : i < (marshalEndpoints 𝓖 T V).card
  · rw [marshalPart, dif_pos h]
    exact marshalEndpoints_le_T 𝓖 T V hle _ (Finset.orderEmbOfFin_mem _ _ _)
  · exact le_of_eq (by rw [marshalPart, dif_neg h])

/-- **Coverage.** The last enumerated cell boundary is `T` (`T` is the maximum, since every endpoint
is `≤ T`). Taking `N = card − 1` gives `marshalPart N = T`, so the partition covers `[0, T]`. -/
lemma marshalPart_card_sub_one (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    marshalPart 𝓖 T V ((marshalEndpoints 𝓖 T V).card - 1) = T := by
  have hpos : 0 < (marshalEndpoints 𝓖 T V).card :=
    Finset.card_pos.mpr (marshalEndpoints_nonempty 𝓖 T V)
  refine le_antisymm ?_ ?_
  · have hlt : (marshalEndpoints 𝓖 T V).card - 1 < (marshalEndpoints 𝓖 T V).card := by omega
    rw [marshalPart, dif_pos hlt]
    exact marshalEndpoints_le_T 𝓖 T V hle _ (Finset.orderEmbOfFin_mem _ _ _)
  · obtain ⟨k, hk_card, hk⟩ := exists_marshalPart_eq 𝓖 T V (T_mem_marshalEndpoints 𝓖 T V)
    calc T = marshalPart 𝓖 T V k := hk.symm
      _ ≤ marshalPart 𝓖 T V ((marshalEndpoints 𝓖 T V).card - 1) :=
          marshalPart_mono 𝓖 T V hle (by omega)

/-- **Cell-constancy.** On the enumerated cell `(sᵢ, sᵢ₊₁]` the step process `V` is constant, equal to
the per-cell multiplier: `⇑V t ω = marshalMult i ω` for `t` in the cell. (The `⊥` atom of `apply_eq`
drops since `t > sᵢ ≥ 0`; each interval indicator matches the covering test via `mem_Ioc_iff_cover`.) -/
lemma marshalMult_eq_uncurry (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {i : ℕ} {t : ℝ≥0} (ht1 : marshalPart 𝓖 T V i < t)
    (ht2 : t ≤ marshalPart 𝓖 T V (i + 1)) (ω : Ω) :
    ⇑V t ω = marshalMult 𝓖 T V i ω := by
  have ht0 : t ∉ ({⊥} : Set ℝ≥0) := by
    simp only [Set.mem_singleton_iff]
    exact (lt_of_le_of_lt zero_le ht1).ne'
  rw [SimpleProcess.apply_eq, Set.indicator_of_notMem ht0, zero_add, Finsupp.sum, marshalMult]
  refine Finset.sum_congr rfl (fun p hp ↦ ?_)
  rw [Set.indicator_apply]
  by_cases hmem : t ∈ Set.Ioc p.1 p.2
  · rw [if_pos hmem, if_pos ((mem_Ioc_iff_cover 𝓖 T V hle ht1 ht2 hp).mp hmem)]
  · rw [if_neg hmem, if_neg (fun hc ↦ hmem ((mem_Ioc_iff_cover 𝓖 T V hle ht1 ht2 hp).mpr hc))]

/-- **Partition of unity.** The marshalled cells `(sᵢ, sᵢ₊₁]`, `i < N`, cover `(0, s_N]` disjointly:
their indicators sum to `1` at any `s ∈ (0, T]` (with `s_N = T`). Proved by telescoping
`𝟙_{(a,b]} = 𝟙_{Iic b} − 𝟙_{Iic a}`. -/
lemma sum_cell_indicator_eq_one (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {N : ℕ} (hmpN : marshalPart 𝓖 T V N = T) {s : ℝ≥0} (hs0 : 0 < s) (hsT : s ≤ T) :
    ∑ i ∈ Finset.range N,
      (Set.Ioc (marshalPart 𝓖 T V i) (marshalPart 𝓖 T V (i + 1))).indicator
        (fun _ ↦ (1 : ℝ)) s = 1 := by
  have hsub : ∀ i,
      (Set.Ioc (marshalPart 𝓖 T V i) (marshalPart 𝓖 T V (i + 1))).indicator
          (fun _ ↦ (1 : ℝ)) s
      = (Set.Iic (marshalPart 𝓖 T V (i + 1))).indicator (fun _ ↦ (1 : ℝ)) s
        - (Set.Iic (marshalPart 𝓖 T V i)).indicator (fun _ ↦ (1 : ℝ)) s := fun i ↦ by
    have hab := marshalPart_mono 𝓖 T V hle (Nat.le_succ i)
    simp only [Set.indicator_apply, Set.mem_Ioc, Set.mem_Iic]
    by_cases h1 : s ≤ marshalPart 𝓖 T V i
    · rw [if_neg (fun h ↦ absurd h.1 (not_lt.mpr h1)), if_pos (h1.trans hab), if_pos h1]; ring
    · rw [not_le] at h1
      by_cases h2 : s ≤ marshalPart 𝓖 T V (i + 1)
      · rw [if_pos ⟨h1, h2⟩, if_pos h2, if_neg (not_le.mpr h1)]; ring
      · rw [not_le] at h2
        rw [if_neg (fun h ↦ absurd h.2 (not_le.mpr h2)), if_neg (not_le.mpr h2),
          if_neg (not_le.mpr (hab.trans_lt h2))]; ring
  simp_rw [hsub]
  rw [Finset.sum_range_sub (fun i ↦ (Set.Iic (marshalPart 𝓖 T V i)).indicator (fun _ ↦ (1 : ℝ)) s),
    hmpN, marshalPart_zero 𝓖 T V hle,
    Set.indicator_of_mem (Set.mem_Iic.mpr hsT),
    Set.indicator_of_notMem (by simp only [Set.mem_Iic, not_le]; exact hs0)]
  norm_num

theorem marshalMult_norm_le (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (V : SimpleProcess E 𝓖) (i : ℕ) (ω : Ω) :
    ‖marshalMult 𝓖 T V i ω‖ ≤ (V.value.support.card : ℝ) * V.valueBound := by
  unfold marshalMult
  calc
    _ ≤ ∑ p ∈ V.value.support,
        ‖if p.1 ≤ marshalPart 𝓖 T V i ∧ marshalPart 𝓖 T V (i + 1) ≤ p.2
          then V.value p ω else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ V.value.support, V.valueBound := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · exact V.value_le_valueBound p ω
      · simpa using V.valueBound_nonneg
    _ = _ := by simp

/-- The same partition reconstructs any function of the row inside
its cells. In particular, it reconstructs both the row and its squared
norm, with no linearity or smoothness assumption on that function. -/
theorem sum_cells_map {G : Type*} [AddCommMonoid G] [Module ℝ G]
    (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (V : SimpleProcess E 𝓖)
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) {N : ℕ}
    (hN : marshalPart 𝓖 T V N = T) {r : ℝ≥0} (hr0 : 0 < r) (hrT : r ≤ T)
    (f : E → G) (ω : Ω) :
    (∑ i ∈ Finset.range N,
      (Set.Ioc (marshalPart 𝓖 T V i) (marshalPart 𝓖 T V (i + 1))).indicator
        (fun _ ↦ f (marshalMult 𝓖 T V i ω)) r) = f (V r ω) := by
  have he (i : ℕ) :
      (Set.Ioc (marshalPart 𝓖 T V i) (marshalPart 𝓖 T V (i + 1))).indicator
        (fun _ ↦ f (marshalMult 𝓖 T V i ω)) r =
      (Set.Ioc (marshalPart 𝓖 T V i) (marshalPart 𝓖 T V (i + 1))).indicator
        (fun _ ↦ (1 : ℝ)) r • f (V r ω) := by
    by_cases hm : r ∈ Set.Ioc (marshalPart 𝓖 T V i) (marshalPart 𝓖 T V (i + 1))
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_smul,
        ← marshalMult_eq_uncurry 𝓖 T V hle hm.1 hm.2 ω]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_smul]
  simp_rw [he]
  rw [← Finset.sum_smul, sum_cell_indicator_eq_one 𝓖 T V hle hN hr0 hrT, one_smul]

end SHEStochastic.FilteredSimplePartition
