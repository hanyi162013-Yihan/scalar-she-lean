module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.FiniteOrthonormalSums
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {κ E C : Type*} [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def value (v : κ → E) (x : κ → ℝ) : E := ∑ i, x i • v i

theorem norm_sq (v : κ → E) (hv : Orthonormal ℝ v) (x : κ → ℝ) :
    ‖value v x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [value, pow_two, conj_trivial] using hv.inner_sum x x Finset.univ

theorem coefficient_le (v : κ → E) (hv : Orthonormal ℝ v) (x : κ → ℝ) (i : κ) :
    |x i| ≤ ‖value v x‖ := by
  have hh := norm_inner_le_norm (𝕜 := ℝ) (v i) (value v x)
  rw [hv.norm_eq_one i, one_mul] at hh
  have he : inner ℝ (v i) (value v x) = x i := hv.inner_right_fintype x i
  simpa only [he, Real.norm_eq_abs] using hh

/-- Finite Hilbert row Cauchy--Schwarz, with no dimension factor. -/
theorem weighted_row_sq [NormedAddCommGroup C] [NormedSpace ℝ C] (x : κ → ℝ) (R : κ → C) :
    ‖∑ i, x i • R i‖ ^ 2 ≤ (∑ i, x i ^ 2) * ∑ i, ‖R i‖ ^ 2 := by
  have hh : ‖∑ i, x i • R i‖ ≤ ∑ i, |x i| * ‖R i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i ↦ x i • R i)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ |x i|) (fun i ↦ ‖R i‖)
  simpa only [sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans hc

section Martingale
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [CompleteSpace E]

theorem map_scalar (X : ℝ≥0 → Ω → ℝ) (hX : Martingale X F μ) (v : E) :
    Martingale (fun t ω ↦ X t ω • v) F μ := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ v
  refine ⟨fun t ↦ L.continuous.comp_stronglyMeasurable (hX.stronglyMeasurable t), ?_⟩
  intro s t hst
  exact (L.comp_condExp_comm (hX.integrable t)).symm.trans
    ((hX.condExp_ae_eq hst).fun_comp L)

theorem martingale (v : κ → E) (X : κ → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, Martingale (X i) F μ) :
    Martingale (fun t ω ↦ value v (fun i ↦ X i t ω)) F μ := by
  classical
  have hs (s : Finset κ) : Martingale (fun t ω ↦ ∑ i ∈ s, X i t ω • v i) F μ := by
    induction s using Finset.induction with
    | empty => simpa only [Finset.sum_empty, Pi.zero_def] using martingale_zero E F μ
    | @insert i s hi ih =>
        simpa only [Finset.sum_insert hi, Pi.add_def] using (map_scalar (X i) (hX i) (v i)).add ih
  exact hs Finset.univ

theorem continuous (v : κ → E) (X : κ → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i ω, Continuous (X i · ω)) (ω : Ω) :
    Continuous (fun t ↦ value v (fun i ↦ X i t ω)) := by
  exact continuous_finset_sum Finset.univ (fun i _ ↦ (hX i ω).smul continuous_const)

theorem memLp (v : κ → E) (X : κ → Ω → ℝ) (p : ℝ≥0∞) (hX : ∀ i, MemLp (X i) p μ) :
    MemLp (fun ω ↦ value v (fun i ↦ X i ω)) p μ := by
  have hh := memLp_finsetSum Finset.univ (fun i _ ↦
    (ContinuousLinearMap.toSpanSingleton ℝ (v i)).comp_memLp' (hX i))
  simpa only [value, Finset.sum_apply, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using hh

end Martingale
end SHEStochastic.FiniteOrthonormalSums
