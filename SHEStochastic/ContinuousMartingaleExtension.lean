/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Abstracts the verified fast-approximation / weak-Doob / Borel-Cantelli
proof from formal-mathfin, 3c41aee9bf2d9743f9e66b439f90d1635843d2d2,
ItoIntegralProcessContinuousModification.lean. Brownian assumptions are
replaced by the precise dense continuous-martingale approximation data,
so one proof serves scalar and cylindrical finite-horizon integration.
-/
module

public import SHEStochastic.FilteredItoProcessGeneral
public import BrownianMotion.StochasticIntegral.DoobLp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.ContinuousMartingaleExtension
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
variable {Ω A V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [AddCommGroup V] [Module ℝ V]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0}

/-- Deterministic approximation data and ordinary continuous martingales.
This is an intermediate construction interface, not an accepted axiom. -/
structure Model (A V : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [AddCommGroup V] [Module ℝ V]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0) where
  embedding : V →ₗ[ℝ] A
  dense : DenseRange embedding
  process : V →ₗ[ℝ] (ℝ≥0 → Ω → ℝ)
  martingale : ∀ v, Martingale (process v) F μ
  continuous : ∀ v ω, Continuous (fun t ↦ process v t ω)
  atTime : ℝ≥0 → A →L[ℝ] Lp ℝ 2 μ
  representative : ∀ v t, (atTime t (embedding v) : Ω → ℝ) =ᵐ[μ] process v t
  terminal_bound : ∀ v, ‖atTime H (embedding v)‖ ≤ ‖embedding v‖

namespace Model
variable (M : Model A V F μ H)

theorem memLp (v : V) (t : ℝ≥0) : MemLp (M.process v t) 2 μ :=
  (memLp_congr_ae (M.representative v t)).mp (Lp.memLp (M.atTime t (M.embedding v)))

theorem maximal_prob (v : V) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ ⨆ i : Set.Iic H, ‖M.process v i ω‖} ≤ ε⁻¹ * ‖M.embedding v‖ := by
  let S := {ω | ε ≤ ⨆ i : Set.Iic H, ‖M.process v i ω‖}
  have hf := M.memLp v H
  have hfi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hw := maximal_ineq_norm (M.martingale v) ε H
    (fun ω _ ↦ (M.continuous v ω).continuousWithinAt)
  have hi : ∫ ω in S, ‖M.process v H ω‖ ∂μ ≤ ∫ ω, ‖M.process v H ω‖ ∂μ :=
    setIntegral_le_integral hfi.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
  have hL2 : ∫ ω, ‖M.process v H ω‖ ∂μ ≤ ‖M.atTime H (M.embedding v)‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (M.representative v H),
      ← ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
      ofReal_integral_norm_eq_lintegral_enorm hfi,
      ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact ENNReal.toReal_mono hf.ne (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
  rw [smul_eq_mul] at hw
  have hc : ε * μ.real S ≤ ‖M.embedding v‖ := hw.trans (hi.trans (hL2.trans (M.terminal_bound v)))
  calc μ.real S = ε⁻¹ * (ε * μ.real S) := by
        rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hε.le)

theorem approxSeq (a : A) : ∃ v : ℕ → V,
    ∀ n, ‖M.embedding (v n) - a‖ ≤ (2⁻¹ : ℝ) ^ n := by
  have he (n : ℕ) : ∃ v : V, ‖M.embedding v - a‖ ≤ (2⁻¹ : ℝ) ^ n := by
    obtain ⟨v, hv⟩ := M.dense.exists_dist_lt a (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ n)
    exact ⟨v, by rw [← dist_eq_norm, dist_comm]; exact hv.le⟩
  choose v hv using he
  exact ⟨v, hv⟩

theorem summable_maximal_tail (a : A) (v : ℕ → V)
    (hv : ∀ n, ‖M.embedding (v n) - a‖ ≤ (2⁻¹ : ℝ) ^ n) :
    Summable (fun n ↦ μ.real {ω | (3 / 4 : ℝ) ^ n ≤
      ⨆ i : Set.Iic H, ‖M.process (v n - v (n + 1)) i ω‖}) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one (r := 2 / 3) (by norm_num) (by norm_num)).mul_left 2)
  refine (M.maximal_prob (v n - v (n + 1)) (ε := (3 / 4 : ℝ) ^ n) (by positivity)).trans ?_
  have hn : ‖M.embedding (v n - v (n + 1))‖ ≤ 2 * (2⁻¹ : ℝ) ^ n := by
    rw [map_sub]
    calc ‖M.embedding (v n) - M.embedding (v (n + 1))‖
        ≤ ‖M.embedding (v n) - a‖ + ‖a - M.embedding (v (n + 1))‖ := by
          simpa using norm_add_le (M.embedding (v n) - a) (a - M.embedding (v (n + 1)))
      _ ≤ (2⁻¹ : ℝ) ^ n + (2⁻¹ : ℝ) ^ (n + 1) := by
          gcongr
          · exact hv n
          · rw [norm_sub_rev]; exact hv (n + 1)
      _ ≤ _ := by rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) n]
  calc ((3 / 4 : ℝ) ^ n)⁻¹ * ‖M.embedding (v n - v (n + 1))‖
      ≤ ((3 / 4 : ℝ) ^ n)⁻¹ * (2 * (2⁻¹ : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 2 * (2 / 3 : ℝ) ^ n := by
        rw [← inv_pow, mul_comm (2 : ℝ) ((2⁻¹ : ℝ) ^ n), ← mul_assoc, ← mul_pow,
          show ((3 / 4 : ℝ)⁻¹ * 2⁻¹) = 2 / 3 from by norm_num, mul_comm]

theorem ae_eventually_sup_lt (a : A) (v : ℕ → V)
    (hv : ∀ n, ‖M.embedding (v n) - a‖ ≤ (2⁻¹ : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      (⨆ i : Set.Iic H, ‖M.process (v n - v (n + 1)) i ω‖) < (3 / 4 : ℝ) ^ n := by
  let S : ℕ → Set Ω := fun n ↦ {ω | (3 / 4 : ℝ) ^ n ≤
    ⨆ i : Set.Iic H, ‖M.process (v n - v (n + 1)) i ω‖}
  have hc : (∑' n, μ (S n)) ≠ ∞ := by
    have he (n) : μ (S n) = ENNReal.ofReal (μ.real (S n)) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ measureReal_nonneg)
      (M.summable_maximal_tail a v hv)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hc] with ω hω
  filter_upwards [hω] with n hn
  exact not_le.mp hn

theorem norm_le_iSup (v : V) (ω : Ω) {t : ℝ≥0} (ht : t ≤ H) :
    ‖M.process v t ω‖ ≤ ⨆ i : Set.Iic H, ‖M.process v i ω‖ := by
  have hc : Continuous fun i : Set.Iic H ↦ ‖M.process v i ω‖ :=
    (continuous_norm.comp (M.continuous v ω)).comp continuous_subtype_val
  have he : (Set.Iic H : Set ℝ≥0) = Set.Icc 0 H := by ext x; simp
  letI : CompactSpace (Set.Iic H) := isCompact_iff_compactSpace.mp (he ▸ isCompact_Icc)
  exact le_ciSup (isCompact_range hc).bddAbove ⟨t, ht⟩

def continuousMod (a : A) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop fun n ↦ M.process ((M.approxSeq a).choose n) t ω

theorem continuousMod_tendsto (a : A) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ H →
      Tendsto (fun n ↦ M.process ((M.approxSeq a).choose n) t ω) atTop
        (𝓝 (M.continuousMod a t ω)) := by
  let v := (M.approxSeq a).choose
  have hv := (M.approxSeq a).choose_spec
  filter_upwards [M.ae_eventually_sup_lt a v hv] with ω hω
  intro t ht
  have hc : CauchySeq (fun n ↦ M.process (v n) t ω) := by
    apply cauchySeq_of_summable_dist
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
      (f := fun n ↦ (3 / 4 : ℝ) ^ (n + N)) ?_
    · rw [dist_eq_norm, ← Pi.sub_apply, ← Pi.sub_apply, ← map_sub]
      exact (M.norm_le_iSup (v (n + N) - v (n + N + 1)) ω ht).trans
        (hN (n + N) (Nat.le_add_left N n)).le
    · simp_rw [pow_add]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  exact hc.tendsto_limUnder

theorem continuousMod_modification (a : A) {t : ℝ≥0} (ht : t ≤ H) :
    (fun ω ↦ M.continuousMod a t ω) =ᵐ[μ] M.atTime t a := by
  let v := (M.approxSeq a).choose
  have hv := (M.approxSeq a).choose_spec
  let G : ℕ → Ω → ℝ := fun n ↦ M.process (v n) t
  have hG : ∀ n, MemLp (G n) 2 μ := fun n ↦ M.memLp (v n) t
  have hg : TendstoInMeasure μ G atTop (fun ω ↦ M.continuousMod a t ω) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hG n).aestronglyMeasurable) ?_
    filter_upwards [M.continuousMod_tendsto a] with ω hω using hω t ht
  have he : Tendsto (fun n ↦ M.embedding (v n)) atTop (𝓝 a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hv
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hLp : Tendsto (fun n ↦ (hG n).toLp (G n)) atTop (𝓝 (M.atTime t a)) := by
    have heq (n) : (hG n).toLp (G n) = M.atTime t (M.embedding (v n)) :=
      Lp.ext ((hG n).coeFn_toLp.trans (M.representative (v n) t).symm)
    simp_rw [heq]
    exact ((M.atTime t).continuous.tendsto a).comp he
  have hn : Tendsto (fun n ↦ eLpNorm (G n - ⇑(M.atTime t a)) 2 μ) atTop (𝓝 0) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' G hG
      (⇑(M.atTime t a)) (Lp.memLp _)).mp ?_
    simpa only [Lp.toLp_coeFn] using hLp
  exact tendstoInMeasure_ae_unique hg (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hn)

theorem continuousMod_continuousOn (a : A) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ M.continuousMod a t ω) (Set.Icc 0 H) := by
  let v := (M.approxSeq a).choose
  have hv := (M.approxSeq a).choose_spec
  filter_upwards [M.ae_eventually_sup_lt a v hv, M.continuousMod_tendsto a] with ω hω htends
  rw [show (Set.Icc 0 H : Set ℝ≥0) = Set.Iic H from by ext x; simp]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  have hu : TendstoUniformlyOn (fun n t ↦ M.process (v n) t ω)
      (fun t ↦ M.continuousMod a t ω) atTop (Set.Iic H) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht0 : Tendsto (fun n ↦ 4 * (3 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 4 * 0 from by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 4
    filter_upwards [eventually_ge_atTop N, ht0.eventually_lt_const hε] with n hn hnε
    intro t ht
    rw [Set.mem_Iic] at ht
    rw [dist_comm]
    have hlim := (htends t ht).comp (tendsto_add_atTop_nat n)
    have hs (k : ℕ) : dist (M.process (v (k + n)) t ω) (M.process (v (k + 1 + n)) t ω)
        ≤ (3 / 4 : ℝ) ^ n * (3 / 4 : ℝ) ^ k := by
      rw [show k + 1 + n = (k + n) + 1 from by ring, dist_eq_norm,
        ← Pi.sub_apply, ← Pi.sub_apply, ← map_sub]
      refine (M.norm_le_iSup (v (k + n) - v (k + n + 1)) ω ht).trans ?_
      exact (hN (k + n) (hn.trans (Nat.le_add_left n k))).le.trans
        (le_of_eq (by rw [pow_add]; ring))
    have h0 := dist_le_of_le_geometric_of_tendsto₀ (3 / 4) ((3 / 4 : ℝ) ^ n)
      (by norm_num) hs hlim
    simp only [zero_add] at h0
    refine lt_of_le_of_lt (h0.trans (le_of_eq ?_)) hnε
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 from by norm_num]; ring
  exact hu.continuousOn (Eventually.of_forall fun n ↦ (M.continuous (v n) ω).continuousOn).frequently

/-- Completion of dense continuous elementary martingales has a continuous
modification. No stochastic-calculus theorem is an assumption here. -/
theorem exists_continuous_modification (a : A) :
    ∃ X : ℝ≥0 → Ω → ℝ, (∀ t, t ≤ H → X t =ᵐ[μ] M.atTime t a) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 H)) :=
  ⟨M.continuousMod a, fun _ ht ↦ M.continuousMod_modification a ht,
    M.continuousMod_continuousOn a⟩

end Model
end SHEStochastic.ContinuousMartingaleExtension
