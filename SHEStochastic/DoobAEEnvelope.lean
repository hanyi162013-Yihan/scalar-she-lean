module

public import SHEStochastic.CountableDoobL2
public import SHEStochastic.DoobL2PowerEnvelope
public import Mathlib.Topology.Order.IsLUB

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.DoobAEEnvelope
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {X : ℝ≥0 → Ω → E}

/-- Continuous paths are needed only almost surely: the maximal bound
is proved first on a countable dense set, keeping the original filtration. -/
theorem power_bound (hm : Martingale X F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (X · ω)) (H : ℝ≥0) (p : ℕ)
    (hMom : ∀ t, Integrable (fun ω ↦ ‖X t ω‖ ^ p) μ)
    (hT : MemLp (fun ω ↦ ‖X H ω‖ ^ p) 2 μ) :
    (∫⁻ ω, (⨆ t : Iic H, ENNReal.ofReal (‖X t ω‖ ^ p)) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (‖X H ω‖ ^ (2 * p)) ∂μ := by
  obtain ⟨T, hTc, hTd⟩ := exists_countable_dense (Iic H)
  let S := T ∪ {(⟨H, le_rfl⟩ : Iic H)}
  have hSc : S.Countable := hTc.union (countable_singleton _)
  letI : Countable S := hSc.to_subtype
  let top : S := ⟨⟨H, le_rfl⟩, Or.inr (mem_singleton _)⟩
  have hle (s : S) : s ≤ top := s.1.2
  have hsd : Dense S := hTd.mono subset_union_left
  have hmS := hm.indexComap (show Monotone (fun s : S ↦ (s.1 : ℝ≥0)) from fun _ _ h ↦ h)
  have hh := CountableDoobL2.martingale_norm_power hmS p top
    (fun s ↦ hMom s) hT
  simp only [hle, iSup_pos, Function.comp_def] at hh
  have he : ∀ᵐ ω ∂μ, (⨆ s : S, ENNReal.ofReal (‖X s ω‖ ^ p)) =
      ⨆ t : Iic H, ENNReal.ofReal (‖X t ω‖ ^ p) := by
    filter_upwards [hc] with ω hω
    exact hsd.ciSup' (ENNReal.continuous_ofReal.comp
      (((hω.comp continuous_subtype_val).norm).pow p))
  have hI : (∫⁻ ω, (⨆ s : S, ENNReal.ofReal (‖X s ω‖ ^ p)) ^ 2 ∂μ) =
      ∫⁻ ω, (⨆ t : Iic H, ENNReal.ofReal (‖X t ω‖ ^ p)) ^ 2 ∂μ :=
    lintegral_congr_ae (he.mono fun ω hω ↦ congrArg (fun z : ℝ≥0∞ ↦ z ^ 2) hω)
  rwa [hI] at hh

theorem sup_aemeasurable (hm : Martingale X F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (X · ω)) (H : ℝ≥0) :
    AEMeasurable (fun ω ↦ ⨆ t : Iic H, ‖X t ω‖ₑ) μ := by
  obtain ⟨S, hSc, hSd⟩ := exists_countable_dense (Iic H)
  letI : Countable S := hSc.to_subtype
  have hmS : Measurable (fun ω ↦ ⨆ t : S, ‖X t ω‖ₑ) := Measurable.iSup fun t ↦ by
    simpa only [ofReal_norm] using
      ((hm.stronglyMeasurable t).mono (F.le t)).norm.measurable.ennreal_ofReal
  apply hmS.aemeasurable.congr
  filter_upwards [hc] with ω hω
  exact hSd.ciSup' ((hω.comp continuous_subtype_val).enorm)

/-- A random L² maximum and its attainment hold on one sample event;
no completion hypothesis on the filtration is imposed. -/
theorem exists_envelope (hm : Martingale X F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (X · ω)) (H : ℝ≥0) (hT : MemLp (X H) 2 μ) :
    ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0 ≤ D ω) ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ H → ‖X t ω‖ ≤ D ω) ∧
      ∀ᵐ ω ∂μ, ∃ t : ℝ≥0, t ≤ H ∧ D ω = ‖X t ω‖ := by
  let A (ω : Ω) : ℝ≥0∞ := ⨆ t : Iic H, ‖X t ω‖ₑ
  have hAm : AEMeasurable A μ := sup_aemeasurable hm hc H
  have hAf : ∀ᵐ ω ∂μ, A ω ≠ ∞ := by
    filter_upwards [hc] with ω hω
    have hcomp : IsCompact (Iic H : Set ℝ≥0) := by
      convert isCompact_Icc (a := (0 : ℝ≥0)) (b := H) using 1
      ext x
      simp
    obtain ⟨r, hr⟩ := hcomp.bddAbove_image hω.norm.continuousOn
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply iSup_le
    intro t
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hr (mem_image_of_mem (fun t ↦ ‖X t ω‖) t.property))
  let D (ω : Ω) := (A ω).toReal
  have hDm : AEMeasurable D μ := hAm.ennreal_toReal
  have hEq : ∀ᵐ ω ∂μ, ENNReal.ofReal (D ω ^ 2) = A ω ^ 2 := by
    filter_upwards [hAf] with ω hω
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω]
  have hBound := power_bound hm hc H 1
    (fun t ↦ by simpa only [pow_one] using (hm.integrable t).norm)
    (by simpa only [pow_one] using hT.norm)
  simp only [pow_one, ofReal_norm] at hBound
  have hFinite : (∫⁻ ω, ENNReal.ofReal (‖X H ω‖ ^ 2) ∂μ) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ sq_nonneg _)).mp hT.norm.integrable_sq.2
  have hDlp : MemLp D 2 μ := by
    apply (memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).mpr
    refine ⟨hDm.aestronglyMeasurable.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ sq_nonneg _), lintegral_congr_ae hEq]
    exact hBound.trans_lt (ENNReal.mul_lt_top (by norm_num) hFinite)
  refine ⟨D, hDlp, fun _ ↦ ENNReal.toReal_nonneg, ?_, ?_⟩
  · filter_upwards [hAf] with ω hω
    intro t ht
    have hh : ‖X t ω‖ₑ ≤ A ω := le_iSup (fun s : Iic H ↦ ‖X s ω‖ₑ) ⟨t, ht⟩
    have hr := ENNReal.toReal_mono hω hh
    rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at hr
    exact hr
  · filter_upwards [hc] with ω hω
    have hcomp : IsCompact (Iic H : Set ℝ≥0) := by
      convert isCompact_Icc (a := (0 : ℝ≥0)) (b := H) using 1
      ext x
      simp
    obtain ⟨t, ht, hmax⟩ := hcomp.exists_isMaxOn ⟨(0 : ℝ≥0), by simp⟩ hω.norm.continuousOn
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

theorem bound (hm : Martingale X F μ) (hc : ∀ᵐ ω ∂μ, Continuous (X · ω))
    (H : ℝ≥0) (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ H → ‖X t ω‖ ≤ D ω)
    (hmax : ∀ᵐ ω ∂μ, ∃ t : ℝ≥0, t ≤ H ∧ D ω = ‖X t ω‖)
    (p : ℕ) (hMom : ∀ t, Integrable (fun ω ↦ ‖X t ω‖ ^ p) μ)
    (hT : MemLp (fun ω ↦ ‖X H ω‖ ^ p) 2 μ) :
    MemLp (fun ω ↦ D ω ^ p) 2 μ ∧
      (∫ ω, D ω ^ (2 * p) ∂μ) ≤ 4 * ∫ ω, ‖X H ω‖ ^ (2 * p) ∂μ := by
  apply DoobL2PowerEnvelope.of_extended H D hD hD0 p hT
  have hh := power_bound hm hc H p hMom hT
  have he : ∀ᵐ ω ∂μ, (⨆ t : Iic H, ENNReal.ofReal (‖X t ω‖ ^ p)) =
      ENNReal.ofReal (D ω ^ p) := by
    filter_upwards [hb, hmax] with ω hbω hmω
    apply le_antisymm
    · exact iSup_le fun t ↦ ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (hbω t t.property) p)
    · obtain ⟨t, ht, hmaxω⟩ := hmω
      rw [hmaxω]
      exact le_iSup (fun s : Iic H ↦ ENNReal.ofReal (‖X s ω‖ ^ p)) ⟨t, ht⟩
  have hI : (∫⁻ ω, (⨆ t : Iic H, ENNReal.ofReal (‖X t ω‖ ^ p)) ^ 2 ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (D ω ^ (2 * p)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω, ← ENNReal.ofReal_pow (pow_nonneg (hD0 ω) p), ← pow_mul, Nat.mul_comm p 2]
  rwa [hI] at hh

end SHEStochastic.DoobAEEnvelope
