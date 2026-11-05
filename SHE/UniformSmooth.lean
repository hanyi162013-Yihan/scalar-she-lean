module

public import SHE.SmoothWords

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Uniform bounds on genuine smooth word derivatives. These are the
deterministic domination needed for space-time cutoff Fubini. -/
noncomputable section
namespace SHE.UniformSmooth
open Set MeasureTheory ProbabilityTheory SmoothCylinders GaussianSmooth
open scoped ContDiff

variable {P : Type*} {D E G : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure UniformBoundedSmooth (F : P → E → G) : Prop where
  smooth : ∀ p, ContDiff ℝ ∞ (F p)
  bounds : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ p z, ‖iteratedFDeriv ℝ k (F p) z‖ ≤ M

namespace UniformBoundedSmooth

theorem boundedSmooth {F : P → E → G} (hF : UniformBoundedSmooth F) (p : P) : BoundedSmooth (F p) :=
  ⟨hF.smooth p, fun k => by obtain ⟨M, _, hM⟩ := hF.bounds k; exact ⟨M, hM p⟩⟩

theorem norm_bound {F : P → E → G} (hF : UniformBoundedSmooth F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p z, ‖F p z‖ ≤ M := by
  simpa only [norm_iteratedFDeriv_zero] using hF.bounds 0

theorem fixed {F : E → G} (hF : BoundedSmooth F) : UniformBoundedSmooth (fun _ : P => F) := by
  refine ⟨fun _ => hF.smooth, fun k => ?_⟩
  obtain ⟨M, hM⟩ := hF.bounds k
  exact ⟨max M 0, le_max_right _ _, fun _ z => (hM z).trans (le_max_left _ _)⟩

theorem parameter_const (c : P → G) {M : ℝ} (hM : 0 ≤ M) (hc : ∀ p, ‖c p‖ ≤ M) :
    UniformBoundedSmooth (fun p (_ : E) => c p) := by
  refine ⟨fun _ => contDiff_const, fun k => ⟨M, hM, fun p z => ?_⟩⟩
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hc p
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; exact hM

theorem fderiv {F : P → E → G} (hF : UniformBoundedSmooth F) :
    UniformBoundedSmooth (fun p => fderiv ℝ (F p)) := by
  refine ⟨fun p => (hF.boundedSmooth p).fderiv.smooth, fun k => ?_⟩
  obtain ⟨M, hMn, hM⟩ := hF.bounds (k + 1)
  exact ⟨M, hMn, fun p z => by simpa only [norm_iteratedFDeriv_fderiv] using hM p z⟩

theorem comp_right {F : P → E → G} (hF : UniformBoundedSmooth F) (L : D →L[ℝ] E) :
    UniformBoundedSmooth (fun p z => F p (L z)) := by
  refine ⟨fun p => (hF.boundedSmooth p).comp_right L |>.smooth, fun k => ?_⟩
  obtain ⟨M, hMn, hM⟩ := hF.bounds k
  refine ⟨M * ‖L‖^k, mul_nonneg hMn (pow_nonneg (norm_nonneg _) _), fun p z => ?_⟩
  change ‖iteratedFDeriv ℝ k (F p ∘ L) z‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (hF.smooth p) z (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    mul_le_mul_of_nonneg_right (hM p (L z)) (pow_nonneg (norm_nonneg L) k)

theorem apply_vector {F : P → E → (D →L[ℝ] G)} (hF : UniformBoundedSmooth F)
    (v : P → D) {Q : ℝ} (hQ : 0 ≤ Q) (hv : ∀ p, ‖v p‖ ≤ Q) :
    UniformBoundedSmooth (fun p z => F p z (v p)) := by
  refine ⟨fun p => (hF.smooth p).clm_apply contDiff_const, fun k => ?_⟩
  obtain ⟨M, hMn, hM⟩ := hF.bounds k
  refine ⟨Q * M, mul_nonneg hQ hMn, fun p z => ?_⟩
  exact (norm_iteratedFDeriv_clm_apply_const (hF.smooth p).contDiffAt (by simp)).trans
    (mul_le_mul (hv p) (hM p z) (norm_nonneg _) hQ)

theorem sub {F Q : P → E → G} (hF : UniformBoundedSmooth F) (hQ : UniformBoundedSmooth Q) :
    UniformBoundedSmooth (fun p z => F p z - Q p z) := by
  refine ⟨fun p => (hF.smooth p).sub (hQ.smooth p), fun k => ?_⟩
  obtain ⟨M, hMn, hM⟩ := hF.bounds k
  obtain ⟨N, hNn, hN⟩ := hQ.bounds k
  refine ⟨M + N, add_nonneg hMn hNn, fun p z => ?_⟩
  change ‖iteratedFDeriv ℝ k (F p - Q p) z‖ ≤ M + N
  rw [iteratedFDeriv_sub_apply (i := k) (x := z) ((hF.smooth p).of_le (by simp)).contDiffAt
    ((hQ.smooth p).of_le (by simp)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hM p z) (hN p z))

theorem mul {F Q : P → E → ℝ} (hF : UniformBoundedSmooth F) (hQ : UniformBoundedSmooth Q) :
    UniformBoundedSmooth (fun p z => F p z * Q p z) := by
  choose M hM using hF.bounds
  choose N hN using hQ.bounds
  refine ⟨fun p => (hF.smooth p).mul (hQ.smooth p), fun k => ?_⟩
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M i * N (k - i), ?_, fun p z => ?_⟩
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hM i).1) (hN _).1)
  · apply (norm_iteratedFDeriv_mul_le (hF.smooth p) (hQ.smooth p) z (by simp)).trans
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul (mul_le_mul_of_nonneg_left ((hM i).2 p z) (Nat.cast_nonneg _)) ((hN (k - i)).2 p z)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hM i).1))

section Average
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem average {F : P → E → G} (hF : UniformBoundedSmooth F) (μ : P → Measure E)
    (hμ : ∀ p, IsProbabilityMeasure (μ p)) :
    UniformBoundedSmooth (fun p => GaussianSmooth.average (μ p) (F p)) := by
  refine ⟨fun p => ?_, fun k => ?_⟩
  · letI := hμ p
    exact (BoundedSmooth.average (μ p) (hF.boundedSmooth p)).smooth
  · obtain ⟨M, hMn, hM⟩ := hF.bounds k
    refine ⟨M, hMn, fun p z => ?_⟩
    letI := hμ p
    exact norm_iteratedFDeriv_average_le (μ p) k (hF.boundedSmooth p) (hM p) z

end Average
end UniformBoundedSmooth
end SHE.UniformSmooth
