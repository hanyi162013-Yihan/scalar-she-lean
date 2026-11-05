module

public import SHEStochastic.DoobL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.DoobL2Envelope
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {X : ℝ≥0 → Ω → E}

/-- Doob L² provides an actual random L² bound for every value on a
compact time interval. Continuity makes the supremum finite for every
path, so the bound can be used directly in predictable multiplier rules. -/
theorem exists_envelope (hm : Martingale X F μ) (hc : ∀ ω, Continuous (X · ω))
    (H : ℝ≥0) (hT : MemLp (X H) 2 μ) :
    ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0 ≤ D ω) ∧
      (∀ t : ℝ≥0, t ≤ H → ∀ ω, ‖X t ω‖ ≤ D ω) ∧
      ∀ ω, ∃ t : ℝ≥0, t ≤ H ∧ D ω = ‖X t ω‖ := by
  let A (ω : Ω) : ℝ≥0∞ := ⨆ t : Iic H, ‖X t ω‖ₑ
  have hAm : Measurable A := by
    have he : A = ⨆ t : Iic H, (fun ω ↦ ‖X t ω‖ₑ) := by ext; simp [A]
    rw [he]
    apply measurable_iSup_of_rightContinuous
    · intro ω a
      exact ((hc ω).enorm.isRightContinuous a).comp continuous_subtype_val.continuousWithinAt
        (fun _ ↦ by simp)
    · intro t
      simpa only [ofReal_norm] using
        ((hm.stronglyMeasurable t).mono (F.le t)).norm.measurable.ennreal_ofReal
  have hAf (ω : Ω) : A ω ≠ ∞ := by
    have hcomp : IsCompact (Iic H : Set ℝ≥0) := by
      convert isCompact_Icc (a := (0 : ℝ≥0)) (b := H) using 1
      ext x
      simp
    obtain ⟨r, hr⟩ := hcomp.bddAbove_image (hc ω).norm.continuousOn
    have hb : A ω ≤ ENNReal.ofReal r := by
      apply iSup_le
      intro t
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hr (mem_image_of_mem (fun t ↦ ‖X t ω‖) t.property))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  let D (ω : Ω) := (A ω).toReal
  have hDm : Measurable D := hAm.ennreal_toReal
  have hEq (ω : Ω) : ENNReal.ofReal (D ω ^ 2) = A ω ^ 2 := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hAf ω)]
  have hBound := DoobL2.martingale hm (fun ω ↦ (hc ω).isRightContinuous) H hT
  have hFinite : (∫⁻ ω, ‖X H ω‖ₑ ^ 2 ∂μ) < ∞ := by
    have hh := (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ω ↦ sq_nonneg ‖X H ω‖)).mp hT.norm.integrable_sq.2
    simpa only [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm] using hh
  have hDlp : MemLp D 2 μ := by
    apply (memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).mpr
    refine ⟨hDm.pow_const 2 |>.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω ↦ sq_nonneg (D ω))]
    simp_rw [hEq]
    exact hBound.trans_lt (ENNReal.mul_lt_top (by norm_num) hFinite)
  refine ⟨D, hDlp, fun _ ↦ ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro t ht ω
    have hh : ‖X t ω‖ₑ ≤ A ω := le_iSup (fun s : Iic H ↦ ‖X s ω‖ₑ) ⟨t, ht⟩
    have hreal := ENNReal.toReal_mono (hAf ω) hh
    rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
    exact hreal
  · intro ω
    have hcomp : IsCompact (Iic H : Set ℝ≥0) := by
      convert isCompact_Icc (a := (0 : ℝ≥0)) (b := H) using 1
      ext x
      simp
    obtain ⟨t, ht, hmax⟩ := hcomp.exists_isMaxOn ⟨(0 : ℝ≥0), by simp⟩ (hc ω).norm.continuousOn
    refine ⟨t, ht, ?_⟩
    have he : A ω = ‖X t ω‖ₑ := by
      apply le_antisymm
      · apply iSup_le
        intro s
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hmax s.property)
      · exact le_iSup (fun s : Iic H ↦ ‖X s ω‖ₑ) ⟨t, ht⟩
    change (A ω).toReal = _
    rw [he, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]

/-- The same actual path maximum obeys every even-power Doob estimate;
only the corresponding finite moments of the martingale are needed. -/
theorem power_bound (hm : Martingale X F μ) (hc : ∀ ω, Continuous (X · ω))
    (H : ℝ≥0) (D : Ω → ℝ)
    (hb : ∀ t : ℝ≥0, t ≤ H → ∀ ω, ‖X t ω‖ ≤ D ω)
    (hmax : ∀ ω, ∃ t : ℝ≥0, t ≤ H ∧ D ω = ‖X t ω‖)
    (p : ℕ) (hMom : ∀ t, Integrable (fun ω ↦ ‖X t ω‖ ^ p) μ)
    (hT : MemLp (fun ω ↦ ‖X H ω‖ ^ p) 2 μ) :
    (∫⁻ ω, ENNReal.ofReal (D ω ^ (2 * p)) ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (‖X H ω‖ ^ (2 * p)) ∂μ := by
  have hh := DoobL2.martingale_norm_power hm (fun ω ↦ (hc ω).isRightContinuous) p H hMom hT
  have he (ω : Ω) : (⨆ t : Iic H, ENNReal.ofReal (‖X t ω‖ ^ p)) = ENNReal.ofReal (D ω ^ p) := by
    apply le_antisymm
    · apply iSup_le
      intro t
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hb t t.property ω) p)
    · obtain ⟨t, ht, hmax⟩ := hmax ω
      rw [hmax]
      exact le_iSup (fun s : Iic H ↦ ENNReal.ofReal (‖X s ω‖ ^ p)) ⟨t, ht⟩
  have hD0 (ω : Ω) : 0 ≤ D ω := (norm_nonneg (X 0 ω)).trans (hb 0 zero_le ω)
  simpa only [he, ← ENNReal.ofReal_pow (pow_nonneg (hD0 _) p) 2, ← pow_mul, Nat.mul_comm p 2] using hh

end SHEStochastic.DoobL2Envelope
