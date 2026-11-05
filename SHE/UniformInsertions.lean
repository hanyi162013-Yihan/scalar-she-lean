module

public import SHE.UniformSmooth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual Gaussian insertion words have uniform derivative bounds on
separated-time cutoffs. The variance coefficients here are TOTAL variances. -/
noncomputable section
namespace SHE.UniformInsertions
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion CovarianceMatrix CovarianceEndpoint GaussianItoTest SmoothWords SmoothCylinders UniformSmooth
open GaussianConvolution

abbrev State (n : ℕ) := WordRecursion.State n
variable {P : Type*}

theorem heatRow_norm_bound {n : ℕ} (Z : Fin n → Observation) {δ t : ℝ}
    (hδ : 0 < δ) (hgap : ∀ i, δ ≤ (Z i).target - t) (x : HeatCircle) :
    ‖heatRow Z t x‖ ≤ Real.sqrt n * heatRowBound δ := by
  have hB := (heatRowBound_pos hδ).le
  have he (i : Fin n) : |heatRow Z t x i| ≤ heatRowBound δ :=
    heatRow_bound Z hδ hgap (le_rfl : t ≤ t) x i
  have hs : ‖heatRow Z t x‖^2 ≤ (n : ℝ) * heatRowBound δ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin n, heatRowBound δ ^ 2 := Finset.sum_le_sum (fun i _ => by
        have hh := he i
        nlinarith only [abs_le.mp hh, sq_abs (heatRow Z t x i), hB])
      _ = _ := by simp
  have hsq : (Real.sqrt n * heatRowBound δ)^2 = (n : ℝ) * heatRowBound δ^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hB)).mp (hs.trans_eq hsq.symm)

theorem insertion_average_uniform {n : ℕ} {a : ℝ → ℝ} (ha : BoundedSmooth a)
    {F : P → State n → ℝ} (hF : UniformBoundedSmooth F)
    (C : P → Matrix (Fin n) (Fin n) ℝ) (c : P → ℝ × HeatCircle → ℝ)
    (Z : P → Fin n → Observation) (t : P → ℝ) (x : P → HeatCircle)
    {M δ : ℝ} (hM : 0 ≤ M) (hc : ∀ p, |c p (t p, x p)| ≤ M)
    (hδ : 0 < δ) (hgap : ∀ p i, δ ≤ (Z p i).target - t p) :
    UniformBoundedSmooth (fun p => insertion a (c p) (Z p) (t p) (x p)
      (gaussianAverage (C p) (F p))) := by
  let row : P → State n := fun p => heatRow (Z p) (t p) (x p)
  let Q : ℝ := Real.sqrt n * heatRowBound δ
  have hQ : 0 ≤ Q := mul_nonneg (Real.sqrt_nonneg _) (heatRowBound_pos hδ).le
  have hrow (p : P) : ‖row p‖ ≤ Q := heatRow_norm_bound (Z p) hδ (hgap p) (x p)
  have hG := hF.average (fun p => multivariateGaussian (0 : State n) (C p)) (fun _ => inferInstance)
  have hdir := ((hG.fderiv.fderiv.apply_vector row hQ hrow).apply_vector row hQ hrow).comp_right (tailProjection n)
  have hcoef := ((UniformBoundedSmooth.fixed (P := P) ha).comp_right (headProjection n)).sub
    (UniformBoundedSmooth.parameter_const (fun p => c p (t p, x p)) hM
      (fun p => by simpa only [Real.norm_eq_abs] using hc p))
  have hhalf := UniformBoundedSmooth.parameter_const (P := P) (E := State (n + 1))
    (fun _ => (1 / 2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2) (fun _ => by norm_num)
  exact (hhalf.mul hcoef).mul hdir

universe u
/-- A family of genuine word histories sharing fixed finite depth. Each
node has a positive separation cutoff, a bounded total reference, and
the exact observation list obtained by appending prior insertion nodes. -/
inductive WordFamily (P : Type u) : {n : ℕ} → (P → Fin n → Observation) → ℕ → Type u
  | nil {n : ℕ} (Z : P → Fin n → Observation) : WordFamily P Z n
  | cons {n m : ℕ} {Z : P → Fin n → Observation}
      (W : P → EndpointWindow n) (same_observations : ∀ p, (W p).observations = Z p)
      (time : P → ℝ) (space : P → HeatCircle) (time_in : ∀ p, time p ∈ Ioo (W p).left (W p).right)
      (before_stops : ∀ p i, (W p).right ≤ (Z p i).stop)
      (δ M : ℝ) (gap_pos : 0 < δ) (upper_nonneg : 0 ≤ M)
      (gap : ∀ p i, δ ≤ (Z p i).target - time p) (upper : ∀ p, (W p).upper ≤ M)
      (rest : WordFamily P (fun p => appendObservation (Z p) (time p) (space p)) m) : WordFamily P Z m

def WordFamily.apply {n m : ℕ} {Z : P → Fin n → Observation}
    (word : WordFamily P Z m) (a : ℝ → ℝ) (F : P → State n → ℝ) : P → State m → ℝ :=
  match word with
  | .nil _ => F
  | .cons W _ t x _ _ _ _ _ _ _ _ rest => rest.apply a
      (fun p => insertion a (W p).coefficient (Z p) (t p) (x p) (backward (W p) (F p) (t p)))

theorem WordFamily.uniform {n m : ℕ} {Z : P → Fin n → Observation}
    (word : WordFamily P Z m) {a : ℝ → ℝ} (ha : BoundedSmooth a)
    {F : P → State n → ℝ} (hF : UniformBoundedSmooth F) :
    UniformBoundedSmooth (word.apply a F) := by
  induction word with
  | nil Z => exact hF
  | cons W hZ t x ht hstop δ M hδ hM hgap hupper rest ih =>
    apply ih
    exact insertion_average_uniform ha hF (fun p => ((W p).path (t p)).val)
      (fun p => (W p).coefficient) _ t x hM
      (fun p => ((W p).bounded (t p) (Ioo_subset_Icc_self (ht p)) (x p)).trans (hupper p)) hδ hgap

/-- The actual cutoff word values are integrable against any finite
history/probability measure once their Borel realization is supplied.
Uniform domination is derived above, not assumed as a word estimate. -/
theorem WordFamily.integrable {n m : ℕ} {Z : P → Fin n → Observation} [MeasurableSpace P]
    (word : WordFamily P Z m) {a : ℝ → ℝ} (ha : BoundedSmooth a)
    {F : P → State n → ℝ} (hF : UniformBoundedSmooth F) (μ : Measure P) [IsFiniteMeasure μ]
    (Y : P → State m) (hvalue : Measurable (fun p => word.apply a F p (Y p))) :
    Integrable (fun p => word.apply a F p (Y p)) μ := by
  obtain ⟨M, _, hM⟩ := (word.uniform ha hF).norm_bound
  exact (integrable_const M).mono' hvalue.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => hM p (Y p)))

end SHE.UniformInsertions
