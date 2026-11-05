module

public import SHE.FiniteMomentSum
public import SHE.GaussianFreshSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.FiniteAssignmentMoments
open MeasureTheory Real
open scoped BigOperators

theorem map_sum_eq_fin {ι : Type*} (is : List ι) (f : ι→ℝ) :
    (is.map f).sum=∑ i : Fin is.length,f (is.get i) := by
  have he := congrArg (fun l : List ι => l.map f) (List.ofFn_get is)
  simp only [List.map_ofFn] at he
  rw [←he,Fin.sum_ofFn]
  simp only [Function.comp_apply]

theorem abs_sum_pow_le {ι : Type*} (is : List ι) (f : ι→ℝ) (b : ℕ) (hb : 0<b) :
    |(is.map f).sum|^(2*b)≤(is.length:ℝ)^(2*b-1)*(is.map (fun i => |f i|^(2*b))).sum := by
  have hpoint := GaussianFreshSum.abs_sum_le is f (fun i => |f i|) (fun _ _ => le_rfl)
  have hh := pow_le_pow_left₀ (abs_nonneg _) hpoint (2*b)
  rw [map_sum_eq_fin] at hh
  rw [map_sum_eq_fin is f]
  refine hh.trans ?_
  have hs := FiniteMomentSum.sum_pow_le (2*b) (by omega) (fun i : Fin is.length => |f (is.get i)|)
    (fun _ => abs_nonneg _)
  rw [map_sum_eq_fin is (fun i => |f i|^(2*b)),map_sum_eq_fin is (fun i => |f i|)]
  simpa only [Fintype.card_fin] using hs

/-- A finite correlated assignment sum retains the sum of its individual
physical moment scales. Only a finite counting constant is lost; no
root clip or selected rough gap is replaced by a common maximum. -/
theorem moment_sum {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (is : List ι) (f : ι→Ω→ℝ) (hf : ∀ i∈is,Measurable (f i)) (b : ℕ) (hb : 0<b)
    (hi : ∀ i∈is,Integrable (fun ω => |f i ω|^(2*b)) μ)
    (C : ι→ℝ) (hC : ∀ i∈is,(∫ ω,|f i ω|^(2*b) ∂μ)≤C i) :
    Integrable (fun ω => |(is.map (fun i => f i ω)).sum|^(2*b)) μ ∧
      (∫ ω,|(is.map (fun i => f i ω)).sum|^(2*b) ∂μ)≤
        (is.length:ℝ)^(2*b-1)*(is.map C).sum := by
  let B := fun ω => (is.length:ℝ)^(2*b-1)*(is.map (fun i => |f i ω|^(2*b))).sum
  have hB : Integrable B μ := (GaussianFreshSum.integrable_sum μ is _ hi).const_mul _
  have hsum : Measurable (fun ω => (is.map (fun i => f i ω)).sum) := by
    have he : (fun ω => (is.map (fun i => f i ω)).sum)=fun ω => ∑ i : Fin is.length,f (is.get i) ω :=
      funext (fun _ => map_sum_eq_fin _ _)
    rw [he]
    exact Finset.measurable_sum Finset.univ (fun i _ => hf _ (List.get_mem _ _))
  have hpow := (continuous_abs.measurable.comp hsum).pow_const (2*b)
  have hir : Integrable (fun ω => |(is.map (fun i => f i ω)).sum|^(2*b)) μ :=
    hB.mono' hpow.aestronglyMeasurable (ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact abs_sum_pow_le is (fun i => f i ω) b hb))
  refine ⟨hir,(integral_mono hir hB (fun ω => abs_sum_pow_le is (fun i => f i ω) b hb)).trans ?_⟩
  dsimp [B]
  rw [integral_const_mul,GaussianFreshSum.integral_sum μ is _ hi]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (le_abs_self _).trans (GaussianFreshSum.abs_sum_le is _ C (fun i hi => by
    rw [abs_of_nonneg (integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _))]
    exact hC i hi))

end SHE.FiniteAssignmentMoments
