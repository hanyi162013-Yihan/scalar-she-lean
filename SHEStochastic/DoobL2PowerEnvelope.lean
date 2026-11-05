module

public import SHEStochastic.DoobL2Envelope

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.DoobL2PowerEnvelope
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {X : ℝ≥0 → Ω → E}

theorem of_extended (H : ℝ≥0) (D : Ω → ℝ) (hD : MemLp D 2 μ)
    (hD0 : ∀ ω, 0 ≤ D ω) (p : ℕ)
    (hT : MemLp (fun ω ↦ ‖X H ω‖ ^ p) 2 μ)
    (hh : (∫⁻ ω, ENNReal.ofReal (D ω ^ (2 * p)) ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (‖X H ω‖ ^ (2 * p)) ∂μ) :
    MemLp (fun ω ↦ D ω ^ p) 2 μ ∧
      (∫ ω, D ω ^ (2 * p) ∂μ) ≤ 4 * ∫ ω, ‖X H ω‖ ^ (2 * p) ∂μ := by
  have hTInt : Integrable (fun ω ↦ ‖X H ω‖ ^ (2 * p)) μ := by
    have hh := hT.integrable_sq
    simpa only [← pow_mul, Nat.mul_comm p 2] using hh
  have hFinite : (∫⁻ ω, ENNReal.ofReal (‖X H ω‖ ^ (2 * p)) ∂μ) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ pow_nonneg (norm_nonneg _) _)).mp hTInt.2
  have hDI : Integrable (fun ω ↦ D ω ^ (2 * p)) μ := by
    refine ⟨hD.aestronglyMeasurable.pow _, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω ↦ pow_nonneg
      (hD0 ω) _)]
    exact hh.trans_lt (ENNReal.mul_lt_top (by norm_num) hFinite)
  have hDp : MemLp (fun ω ↦ D ω ^ p) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hD.aestronglyMeasurable.pow p)).mpr
    change Integrable (fun ω ↦ (D ω ^ p) ^ 2) μ
    simpa only [← pow_mul, Nat.mul_comm p 2] using hDI
  refine ⟨hDp, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hDI (Eventually.of_forall fun ω ↦ pow_nonneg
      (hD0 ω) _),
    ← ofReal_integral_eq_lintegral_ofReal hTInt (Eventually.of_forall fun _ ↦ pow_nonneg (norm_nonneg _) _)] at hh
  have hnonneg : 0 ≤ ∫ ω, ‖X H ω‖ ^ (2 * p) ∂μ := integral_nonneg fun _ ↦ pow_nonneg (norm_nonneg _) _
  have he : (4 : ℝ≥0∞) * ENNReal.ofReal (∫ ω, ‖X H ω‖ ^ (2 * p) ∂μ) =
      ENNReal.ofReal (4 * ∫ ω, ‖X H ω‖ ^ (2 * p) ∂μ) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  rw [he] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) hnonneg)).mp hh

theorem bound (hm : Martingale X F μ) (hc : ∀ ω, Continuous (X · ω))
    (H : ℝ≥0) (D : Ω → ℝ) (hD : MemLp D 2 μ)
    (hb : ∀ t : ℝ≥0, t ≤ H → ∀ ω, ‖X t ω‖ ≤ D ω)
    (hmax : ∀ ω, ∃ t : ℝ≥0, t ≤ H ∧ D ω = ‖X t ω‖)
    (p : ℕ) (hMom : ∀ t, Integrable (fun ω ↦ ‖X t ω‖ ^ p) μ)
    (hT : MemLp (fun ω ↦ ‖X H ω‖ ^ p) 2 μ) :
    MemLp (fun ω ↦ D ω ^ p) 2 μ ∧
      (∫ ω, D ω ^ (2 * p) ∂μ) ≤ 4 * ∫ ω, ‖X H ω‖ ^ (2 * p) ∂μ := by
  exact of_extended H D hD
    (fun ω ↦ (norm_nonneg (X 0 ω)).trans (hb 0 zero_le ω)) p hT
    (DoobL2Envelope.power_bound hm hc H D hb hmax p hMom hT)

end SHEStochastic.DoobL2PowerEnvelope
