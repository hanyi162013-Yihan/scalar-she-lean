module

public import SHE.SmoothCylinders

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SHE.SmoothCylinders
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff

variable {D E G : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace BoundedSmooth

theorem const (c : G) : BoundedSmooth (fun _ : E => c) := by
  refine ⟨contDiff_const, fun k => ⟨‖c‖, fun z => ?_⟩⟩
  cases k with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, norm_nonneg]

theorem comp_left {F : E → G} (hF : BoundedSmooth F) (L : G →L[ℝ] D) :
    BoundedSmooth (fun z => L (F z)) := by
  refine ⟨L.contDiff.comp hF.smooth, fun k => ?_⟩
  obtain ⟨M, hM⟩ := hF.bounds k
  refine ⟨‖L‖ * M, fun z => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left hF.smooth.contDiffAt (by simp)).trans
    (mul_le_mul_of_nonneg_left (hM z) (norm_nonneg _))

theorem comp_right {F : E → G} (hF : BoundedSmooth F) (L : D →L[ℝ] E) :
    BoundedSmooth (fun z => F (L z)) := by
  refine ⟨hF.smooth.comp L.contDiff, fun k => ?_⟩
  obtain ⟨M, hM⟩ := hF.bounds k
  refine ⟨M * ‖L‖ ^ k, fun z => ?_⟩
  change ‖iteratedFDeriv ℝ k (F ∘ L) z‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hF.smooth z (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    mul_le_mul_of_nonneg_right (hM (L z)) (pow_nonneg (norm_nonneg L) k)

theorem sub {F Q : E → G} (hF : BoundedSmooth F) (hQ : BoundedSmooth Q) :
    BoundedSmooth (fun z => F z - Q z) := by
  refine ⟨hF.smooth.sub hQ.smooth, fun k => ?_⟩
  obtain ⟨M, hM⟩ := hF.bounds k
  obtain ⟨N, hN⟩ := hQ.bounds k
  refine ⟨M + N, fun z => ?_⟩
  have he := iteratedFDeriv_sub_apply (i := k) (x := z) (hF.smooth.of_le (by simp)).contDiffAt
    (hQ.smooth.of_le (by simp)).contDiffAt
  change ‖iteratedFDeriv ℝ k (F - Q) z‖ ≤ M + N
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (hM z) (hN z))

theorem mul {F Q : E → ℝ} (hF : BoundedSmooth F) (hQ : BoundedSmooth Q) :
    BoundedSmooth (fun z => F z * Q z) := by
  choose M hM using hF.bounds
  choose N hN using hQ.bounds
  have hMn (k : ℕ) : 0 ≤ M k := (norm_nonneg _).trans (hM k 0)
  refine ⟨hF.smooth.mul hQ.smooth, fun k => ?_⟩
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M i * N (k - i), fun z => ?_⟩
  apply (norm_iteratedFDeriv_mul_le hF.smooth hQ.smooth z (by simp)).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hM i z) (Nat.cast_nonneg _)) (hN (k - i) z)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hMn i))

theorem hessian_lipschitz {F : E → ℝ} (hF : BoundedSmooth F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z w, ‖GaussianTaylor.hessian F w - GaussianTaylor.hessian F z‖ ≤ K * ‖w - z‖ := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  obtain ⟨K, hK⟩ := hF.fderiv.fderiv.fderiv.norm_bound
  refine ⟨K, (norm_nonneg _).trans (hK 0), fun z w => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hF.fderiv.fderiv.smooth.differentiable (by simp) y)
    (fun y _ => hK y) convex_univ (mem_univ z) (mem_univ w)

end BoundedSmooth
end SHE.SmoothCylinders
