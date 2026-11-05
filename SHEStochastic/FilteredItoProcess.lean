/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Adapted from formal-mathfin, 3c41aee9bf2d9743f9e66b439f90d1635843d2d2,
ItoIntegralProcess.lean, replacing the natural filtration by a given Brownian
filtration. The elementary integral is the same public SimpleProcess integral.
-/
module

public import MathFin.Foundations.ItoIntegralProcess
public import SHEStochastic.FilteredItoL2

@[expose] public section
namespace SHEStochastic.FilteredItoProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}

noncomputable def itoSimpleProcess (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (t : ℝ≥0) : Ω → ℝ :=
  SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V B t

private lemma stoppedProcess_const_coe (u s : ℝ≥0) (ω : Ω) :
    stoppedProcess B (fun _ : Ω ↦ u) s ω = B (min s u) ω := rfl

lemma itoSimpleProcess_apply (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas V t ω
      = V.value.sum fun p v ↦ v ω * (B (min p.2 t) ω - B (min p.1 t) ω) := by
  simp only [itoSimpleProcess, SimpleProcess.integral, ContinuousLinearMap.mul_apply']
  refine Finsupp.sum_congr fun p _ ↦ ?_
  rw [stoppedProcess_const_coe, stoppedProcess_const_coe]

lemma itoSimpleProcess_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ 𝓖)
    (t : ℝ≥0) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas (V + W) t = itoSimpleProcess (𝓖 := 𝓖) hBmeas V t
      + itoSimpleProcess (𝓖 := 𝓖) hBmeas W t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_add_left, Pi.add_apply]

lemma itoSimpleProcess_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ 𝓖) (t : ℝ≥0) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas (c • V) t = c • itoSimpleProcess (𝓖 := 𝓖) hBmeas V t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_smul_left, Pi.smul_apply]

lemma itoSimpleProcess_neg (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖) (t : ℝ≥0) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas (-V) t = -itoSimpleProcess (𝓖 := 𝓖) hBmeas V t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_neg_left, Pi.neg_apply]

@[simp] lemma itoSimpleProcess_zero_time (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas V 0 = 0 := by
  funext ω
  rw [itoSimpleProcess_apply (𝓖 := 𝓖), Finsupp.sum]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  have e1 : min p.1 (0 : ℝ≥0) = 0 := min_eq_right zero_le
  have e2 : min p.2 (0 : ℝ≥0) = 0 := min_eq_right zero_le
  rw [e1, e2, sub_self, mul_zero]

lemma itoSimpleProcess_eq_itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    {t : ℝ≥0} (ht : ∀ p ∈ V.value.support, p.2 ≤ t) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas V t = FilteredItoL2.itoSimple (F := 𝓖) hBmeas V := by
  funext ω
  rw [itoSimpleProcess_apply (𝓖 := 𝓖), FilteredItoL2.itoSimple_apply (F := 𝓖)]
  refine Finsupp.sum_congr fun p hp ↦ ?_
  have h2 : min p.2 t = p.2 := min_eq_left (ht p hp)
  have h1 : min p.1 t = p.1 := min_eq_left ((V.le_of_mem_support_value p hp).trans (ht p hp))
  rw [h1, h2]

variable (hB : IsPreBrownianReal B μ)

variable [hFB : IsFilteredPreBrownian B 𝓖 μ]

include hB hFB

theorem memLp_value (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (p : ℝ≥0 × ℝ≥0) : MemLp (V.value p) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact MemLp.of_bound
    ((V.measurable_value p).mono (𝓖.le p.1)
      le_rfl).aestronglyMeasurable
    V.valueBound (ae_of_all _ (V.value_le_valueBound p))

theorem memLp_truncated_term (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (t : ℝ≥0) {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.value.support) :
    MemLp (fun ω ↦ V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω)) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  by_cases ht : p.1 ≤ t
  · -- active interval: adapted coefficient × increment over `[p.1, p.2 ∧ t]`
    rw [min_eq_left ht]
    exact FilteredBrownianCore.memLp_adapted_mul_increment hB hBmeas
      (le_min (V.le_of_mem_support_value p hp) ht)
      (FilteredBrownianCore.adaptedAt_of_measurable hBmeas (V.measurable_value p))
      (memLp_value (𝓖 := 𝓖) hB hBmeas V p)
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
  exact memLp_finsetSum _ fun p hp ↦ memLp_truncated_term (𝓖 := 𝓖) hB hBmeas V t hp

noncomputable def itoSimpleProcessLp (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖)
    (t : ℝ≥0) : Lp ℝ 2 μ :=
  (memLp_itoSimpleProcess (𝓖 := 𝓖) hB hBmeas V t).toLp _


end SHEStochastic.FilteredItoProcess
