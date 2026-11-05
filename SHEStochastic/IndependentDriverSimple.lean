/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Reuse of the elementary L2 and martingale proofs in formal-mathfin,
3c41aee9bf2d9743f9e66b439f90d1635843d2d2, ItoIntegralProcess.lean and
ItoIntegralProcessMartingale.lean. Only independent centered L2 increments
are used, so these proofs apply to native noise frozen after its horizon.
-/
module

public import SHEStochastic.IndependentL2Driver

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.IndependentDriverSimple
open MeasureTheory ProbabilityTheory FilteredItoProcess
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}
  [D : IndependentL2Driver B 𝓖 μ]
include D

theorem memLp_value (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (p : ℝ≥0 × ℝ≥0) : MemLp (V.value p) 2 μ := by
  exact MemLp.of_bound
    ((V.measurable_value p).mono (𝓖.le p.1)
      le_rfl).aestronglyMeasurable
    V.valueBound (ae_of_all _ (V.value_le_valueBound p))

theorem memLp_truncated_term (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (t : ℝ≥0) {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.value.support) :
    MemLp (fun ω ↦ V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω)) 2 μ := by
  by_cases ht : p.1 ≤ t
  · -- active interval: adapted coefficient × increment over `[p.1, p.2 ∧ t]`
    rw [min_eq_left ht]
    exact IndependentL2Driver.memLp_adapted_mul_increment (B := B) (F := 𝓖) (μ := μ)
      (le_min (V.le_of_mem_support_value p hp) ht)
      (FilteredBrownianCore.adaptedAt_of_measurable hBmeas (V.measurable_value p))
      (memLp_value (𝓖 := 𝓖) hBmeas V p)
  · -- interval entirely past `t`: both endpoints truncate to `t`, term is `0`
    push Not at ht
    have h1 : min p.1 t = t := min_eq_right ht.le
    have h2 : min p.2 t = t := min_eq_right (ht.le.trans (V.le_of_mem_support_value p hp))
    simp only [h1, h2, sub_self, mul_zero]
    exact memLp_const 0

theorem memLp_itoSimpleProcess (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (t : ℝ≥0) :
    MemLp (itoSimpleProcess (𝓖 := 𝓖) hBmeas V t) 2 μ := by
  rw [show itoSimpleProcess (𝓖 := 𝓖) hBmeas V t
        = fun ω ↦ ∑ p ∈ V.value.support, V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω)
      from funext fun ω ↦ by rw [itoSimpleProcess_apply (𝓖 := 𝓖)]; rfl]
  exact memLp_finsetSum _ fun p hp ↦ memLp_truncated_term (𝓖 := 𝓖) hBmeas V t hp

noncomputable def itoSimpleProcessLp (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (t : ℝ≥0) : Lp ℝ 2 μ :=
  (memLp_itoSimpleProcess (𝓖 := 𝓖) hBmeas V t).toLp _

theorem itoSimpleProcess_adaptedAt (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖) (t : ℝ≥0) :
    Measurable[𝓖 t] (itoSimpleProcess (𝓖 := 𝓖) hBmeas V t) := by
  have hBmeas_le : ∀ {u : ℝ≥0}, u ≤ t →
      Measurable[𝓖 t] (B u) := by
    intro u hu
    exact (D.adapted u).measurable.mono (𝓖.mono hu) le_rfl
  rw [show itoSimpleProcess (𝓖 := 𝓖) hBmeas V t
        = fun ω ↦ ∑ p ∈ V.value.support,
            V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω)
      from funext fun ω ↦ by rw [itoSimpleProcess_apply (𝓖 := 𝓖)]; rfl]
  refine Finset.measurable_sum _ (fun p hp ↦ ?_)
  by_cases ht : p.1 ≤ t
  · -- active interval: coefficient `𝓕_{p.1} ⊆ 𝓕_t`, both truncated endpoints `≤ t`
    have hV : Measurable[𝓖 t] (V.value p) :=
      (V.measurable_value p).mono (𝓖.mono ht) le_rfl
    exact hV.mul ((hBmeas_le (min_le_right p.2 t)).sub (hBmeas_le (min_le_right p.1 t)))
  · -- interval past `t`: both endpoints truncate to `t`, the term is `0`
    push Not at ht
    have h1 : min p.1 t = t := min_eq_right ht.le
    have h2 : min p.2 t = t := min_eq_right (ht.le.trans (V.le_of_mem_support_value p hp))
    simp only [h1, h2, sub_self, mul_zero]
    exact measurable_const

omit D in
private lemma clamped_increment_eq {u v i j : ℝ≥0} (huv : u ≤ v) (hij : i ≤ j)
    (ω : Ω) :
    (B (min v j) ω - B (min u j) ω) - (B (min v i) ω - B (min u i) ω)
      = B (max (max u i) (min v j)) ω - B (max u i) ω := by
  rcases le_total i u with h1 | h1 <;> rcases le_total j u with h2 | h2 <;>
    rcases le_total i v with h3 | h3 <;> rcases le_total j v with h4 | h4 <;>
      simp_all <;> grind

theorem itoSimpleProcess_isMartingale (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖) :
    Martingale (fun t ω ↦ itoSimpleProcess (𝓖 := 𝓖) hBmeas V t ω)
      𝓖 μ := by
  refine ⟨fun t ↦ (itoSimpleProcess_adaptedAt (𝓖 := 𝓖) (μ := μ) hBmeas V t).stronglyMeasurable, ?_⟩
  intro i j hij
  have hint : ∀ t : ℝ≥0, Integrable (fun ω ↦ itoSimpleProcess (𝓖 := 𝓖) hBmeas V t ω) μ :=
    fun t ↦ (memLp_itoSimpleProcess (𝓖 := 𝓖) hBmeas V t).integrable (by norm_num)
  have hadapt : ∀ p ∈ V.value.support,
      FilteredBrownianCore.AdaptedAt 𝓖 (max p.1 i) (V.value p) := fun p _ ↦
    (FilteredBrownianCore.adaptedAt_of_measurable hBmeas
      (V.measurable_value p)).mono (le_max_left _ _)
  have hVL2 : ∀ p, MemLp (V.value p) 2 μ := fun p ↦ memLp_value (𝓖 := 𝓖) hBmeas V p
  have hle_mM : ∀ p : ℝ≥0 × ℝ≥0,
      max p.1 i ≤ max (max p.1 i) (min p.2 j) := fun _ ↦ le_max_left _ _
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le i)
    (hint j) (fun s _ _ ↦ (hint i).integrableOn) (fun s hs _ ↦ ?_)
    (itoSimpleProcess_adaptedAt (𝓖 := 𝓖) (μ := μ) hBmeas V i).stronglyMeasurable.aestronglyMeasurable
  have hmle : 𝓖 i ≤ mΩ :=
    𝓖.le i
  have hpt : (fun ω ↦ itoSimpleProcess (𝓖 := 𝓖) hBmeas V i ω - itoSimpleProcess (𝓖 := 𝓖) hBmeas V j ω)
      = fun ω ↦ -∑ p ∈ V.value.support,
          V.value p ω * (B (max (max p.1 i) (min p.2 j)) ω - B (max p.1 i) ω) := by
    funext ω
    rw [itoSimpleProcess_apply (𝓖 := 𝓖), itoSimpleProcess_apply (𝓖 := 𝓖), Finsupp.sum, Finsupp.sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hcl := clamped_increment_eq (B := B) (V.le_of_mem_support_value p hp) hij ω
    rw [← mul_sub, ← mul_neg]
    congr 1
    linarith [hcl]
  have hterm_int : ∀ p ∈ V.value.support,
      Integrable (fun ω ↦ V.value p ω
        * (B (max (max p.1 i) (min p.2 j)) ω - B (max p.1 i) ω)) (μ.restrict s) :=
    fun p hp ↦ ((IndependentL2Driver.memLp_adapted_mul_increment (B := B) (F := 𝓖) (μ := μ) (hle_mM p)
      (hadapt p hp) (hVL2 p)).integrable (by norm_num)).integrableOn
  rw [← sub_eq_zero, ← integral_sub (hint i).integrableOn (hint j).integrableOn, hpt,
      integral_neg, neg_eq_zero, integral_finsetSum _ hterm_int]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have hAadapt : FilteredBrownianCore.AdaptedAt 𝓖 (max p.1 i) (s.indicator (V.value p)) := by
    have h1 : FilteredBrownianCore.AdaptedAt 𝓖 (max p.1 i) (s.indicator (1 : Ω → ℝ)) :=
      (FilteredBrownianCore.adaptedAt_of_measurable hBmeas
        ((measurable_const :
          Measurable[𝓖 i] (1 : Ω → ℝ)).indicator hs)).mono
        (le_max_right _ _)
    have heq : (fun ω ↦ s.indicator (1 : Ω → ℝ) ω * V.value p ω) = s.indicator (V.value p) := by
      funext ω; by_cases h : ω ∈ s <;> simp [h]
    exact heq ▸ h1.mul (hadapt p hp)
  rw [← integral_indicator (hmle s hs),
      show (s.indicator fun ω ↦ V.value p ω
            * (B (max (max p.1 i) (min p.2 j)) ω - B (max p.1 i) ω))
          = fun ω ↦ s.indicator (V.value p) ω
            * (B (max (max p.1 i) (min p.2 j)) ω - B (max p.1 i) ω) from by
        funext ω; by_cases h : ω ∈ s <;> simp [h]]
  exact IndependentL2Driver.integral_adapted_mul_increment (B := B) (F := 𝓖) (μ := μ) (hle_mM p) hAadapt


end SHEStochastic.IndependentDriverSimple
