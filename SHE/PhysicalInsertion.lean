module

public import SHE.GaussianItoTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Exact physical mixed-pair cancellation in the finite-dimensional Itô
formula. The terminal heat gap may vanish. -/
noncomputable section
namespace SHE.PhysicalInsertion
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier
open GaussianTaylor GaussianTaylorAverage GaussianConvolution GaussianItoTest
open WordRecursion CovarianceMatrix CovarianceEndpoint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev State (n : ℕ) := WordRecursion.State n

theorem weighted_generator_integrable {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {M s t : ℝ}
    (hM : 0 ≤ M) (ht : t < s) (hgap : ∀ i, s ≤ (Z i).target)
    (hbound : ∀ x, |c (t, x)| ≤ M) (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    Integrable (fun x : HeatCircle => c (t, x) * H (heatRow Z t x) (heatRow Z t x)) haarAddCircle := by
  have hi (i j : Fin n) := covariance_spatial_integrable c hc Z (sub_pos.mpr ht) hM
    (fun i => by linarith [hgap i]) (le_rfl : t ≤ t) hbound i j
  have hs := integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
    (hi i j).mul_const (H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))))
  convert hs using 1
  funext x
  rw [bilinear_mixed_pairs H]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weighted_density_action {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {M s t : ℝ}
    (hM : 0 ≤ M) (ht : t < s) (hgap : ∀ i, s ≤ (Z i).target)
    (hbound : ∀ x, |c (t, x)| ≤ M) (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    covarianceAction (densityMatrix c Z t) H =
      ∫ x : HeatCircle, c (t, x) * H (heatRow Z t x) (heatRow Z t x) ∂haarAddCircle := by
  have hi (i j : Fin n) := covariance_spatial_integrable c hc Z (sub_pos.mpr ht) hM
    (fun i => by linarith [hgap i]) (le_rfl : t ≤ t) hbound i j
  have he (x : HeatCircle) : c (t, x) * H (heatRow Z t x) (heatRow Z t x) =
      ∑ i : Fin n, ∑ j : Fin n, c (t, x) * heatRow Z t x i * heatRow Z t x j *
        H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    rw [bilinear_mixed_pairs H]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => (hi i j).mul_const _))]
  unfold covarianceAction
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => (hi i j).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const]
  rfl

/-- The reference covariance cancels exactly against the physical Itô
bracket, retaining every mixed pair. -/
theorem mixed_pair_cancellation {n : ℕ} (W : EndpointWindow n)
    (d : ℝ × HeatCircle → ℝ) (hd : Measurable d) {A : ℝ} (hA : 0 ≤ A)
    {t : ℝ} (ht : t ∈ Ioo W.left W.right) (hdbound : ∀ x, |d (t, x)| ≤ A)
    (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    -(1 / 2 : ℝ) * covarianceAction (densityMatrix W.coefficient W.observations t) H +
      (1 / 2 : ℝ) * covarianceAction (densityMatrix d W.observations t) H =
      ∫ x : HeatCircle, (1 / 2 : ℝ) * (d (t, x) - W.coefficient (t, x)) *
        H (heatRow W.observations t x) (heatRow W.observations t x) ∂haarAddCircle := by
  have hcint := weighted_generator_integrable W.coefficient W.measurable W.observations
    W.upper_nonneg ht.2 W.target_after (W.bounded t (Ioo_subset_Icc_self ht)) H
  have hdint := weighted_generator_integrable d hd W.observations hA ht.2 W.target_after hdbound H
  rw [weighted_density_action W.coefficient W.measurable W.observations W.upper_nonneg ht.2
    W.target_after (W.bounded t (Ioo_subset_Icc_self ht)),
    weighted_density_action d hd W.observations hA ht.2 W.target_after hdbound]
  have he : (fun x : HeatCircle => (1 / 2 : ℝ) * (d (t, x) - W.coefficient (t, x)) *
        H (heatRow W.observations t x) (heatRow W.observations t x)) =
      fun x => (1 / 2 : ℝ) * (d (t, x) * H (heatRow W.observations t x) (heatRow W.observations t x) -
        W.coefficient (t, x) * H (heatRow W.observations t x) (heatRow W.observations t x)) := by
    funext x
    ring
  rw [he, integral_const_mul]
  have hs := integral_sub hdint hcint
  rw [hs]
  ring

/-- The new coordinate in the operator word is the actual physical state
at the insertion point, including its zero terminal heat age. -/
theorem insertion_generator {n : ℕ} (W : EndpointWindow n)
    (a : ℝ → ℝ) (ha : Measurable a) (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    (hX : Measurable X) {A : ℝ} (hA : 0 ≤ A) (habound : ∀ z, |a z| ≤ A)
    {F : State n → ℝ} {t : ℝ} (ht : t ∈ Ioo W.left W.right) :
    backwardDerivative W F t (observe U X W.observations t) +
      (1 / 2 : ℝ) * covarianceAction (densityMatrix (fun p => a (X p)) W.observations t)
        (GaussianTaylor.hessian (backward W F t) (observe U X W.observations t)) =
      ∫ x : HeatCircle, insertion a W.coefficient W.observations t x (backward W F t)
        (observe U X (appendObservation W.observations t x) t) ∂haarAddCircle := by
  have hh := mixed_pair_cancellation W (fun p => a (X p)) (ha.comp hX) hA ht
    (fun x => habound (X (t, x)))
    (GaussianTaylor.hessian (backward W F t) (observe U X W.observations t))
  rw [show backwardDerivative W F t (observe U X W.observations t) =
    -(1 / 2 : ℝ) * covarianceAction (densityMatrix W.coefficient W.observations t)
      (GaussianTaylor.hessian (backward W F t) (observe U X W.observations t)) from rfl]
  rw [hh]
  apply integral_congr_ae
  filter_upwards with x
  rw [insertion_observe]
  rfl

end SHE.PhysicalInsertion
