module

public import SHE.FiniteAssignmentMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.FiniteAssignmentMoments
open MeasureTheory Real
open scoped BigOperators

/-- A finite sum of later random words may be estimated against one
common correlated nonnegative weight. No normalization of the weighted
measure, or independence of the words and that weight, is required. -/
theorem weighted_moment_sum {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (is : List ι) (f : ι→Ω→ℝ) (hf : ∀ i∈is,Measurable (f i))
    (weight : Ω→ℝ) (hw : Measurable weight) (hw0 : ∀ ω,0≤weight ω)
    (b : ℕ) (hb : 0<b)
    (hi : ∀ i∈is,Integrable (fun ω=>weight ω*|f i ω|^(2*b)) μ)
    (C : ι→ℝ) (hC : ∀ i∈is,(∫ ω,weight ω*|f i ω|^(2*b) ∂μ)≤C i) :
    Integrable (fun ω=>weight ω*|(is.map (fun i=>f i ω)).sum|^(2*b)) μ ∧
      (∫ ω,weight ω*|(is.map (fun i=>f i ω)).sum|^(2*b) ∂μ)≤
        (is.length:ℝ)^(2*b-1)*(is.map C).sum := by
  let B:=fun ω=>(is.length:ℝ)^(2*b-1)*(is.map (fun i=>weight ω*|f i ω|^(2*b))).sum
  have hB : Integrable B μ:=(GaussianFreshSum.integrable_sum μ is _ hi).const_mul _
  have hsum : Measurable (fun ω=>(is.map (fun i=>f i ω)).sum) := by
    have he : (fun ω=>(is.map (fun i=>f i ω)).sum)=
        (fun ω=>∑ i : Fin is.length,f (is.get i) ω):=funext (fun _=>map_sum_eq_fin _ _)
    rw [he]
    exact Finset.measurable_sum Finset.univ (fun i _=>hf _ (List.get_mem _ _))
  have hpoint (ω) : weight ω*|(is.map (fun i=>f i ω)).sum|^(2*b)≤B ω := by
    have hh:=mul_le_mul_of_nonneg_left (abs_sum_pow_le is (fun i=>f i ω) b hb) (hw0 ω)
    simpa only [B,List.sum_map_mul_left,mul_left_comm] using hh
  have hmeas:=hw.mul ((continuous_abs.measurable.comp hsum).pow_const (2*b))
  have hir : Integrable (fun ω=>weight ω*|(is.map (fun i=>f i ω)).sum|^(2*b)) μ:=
    hB.mono' hmeas.aestronglyMeasurable (ae_of_all _ (fun ω=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw0 ω) (pow_nonneg (abs_nonneg _) _))]
      exact hpoint ω))
  refine ⟨hir,(integral_mono hir hB hpoint).trans ?_⟩
  dsimp only [B]
  rw [integral_const_mul,GaussianFreshSum.integral_sum μ is _ hi]
  exact mul_le_mul_of_nonneg_left (List.sum_le_sum (fun i hi=>hC i hi)) (by positivity)

end SHE.FiniteAssignmentMoments
