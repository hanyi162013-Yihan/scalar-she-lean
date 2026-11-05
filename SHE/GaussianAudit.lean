module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import SHE.HistoryFrames
public import Mathlib.Tactic

/-!
# Actual Gaussian scores and finite-word centering

These results use actual Gaussian measures and actual derivatives of their
bounded measurable test integrals. They prove all fixed Gaussian score moments,
singular-compatible covariance-range factorization, physical rank-one mean and
covariance differentiation, finite product-score centering, an explicit
all-order factor assignment expansion, rough-block fractional variance gains,
and actual stopped-history weighted leverage and spatial one-input convolution.

They do not assert the manuscript's complete all-order heat-tree ledger,
continuum covariance-profile derivative, identification and limiting passage
of its stochastic words, or principal uniqueness theorem.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section
namespace SHE.GaussianAudit
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The one-dimensional mean score. -/
def firstScore (v : ℝ≥0) (z : ℝ) : ℝ := z / (v : ℝ)

/-- The one-dimensional covariance score, without the conventional `1/2`. -/
def secondScore (v : ℝ≥0) (z : ℝ) : ℝ :=
  (z ^ 2 - (v : ℝ)) / (v : ℝ) ^ 2

theorem integrable_firstScore (v : ℝ≥0) :
    Integrable (firstScore v) (gaussianReal 0 v) := by
  change Integrable (fun z : ℝ => z / (v : ℝ)) (gaussianReal 0 v)
  simpa only [div_eq_mul_inv, id_eq] using
    (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable (by norm_num) |>.mul_const
      ((v : ℝ)⁻¹)

theorem integral_firstScore (v : ℝ≥0) :
    ∫ z, firstScore v z ∂gaussianReal 0 v = 0 := by
  simp [firstScore, integral_div]

theorem gaussian_second_moment (v : ℝ≥0) :
    ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- The first score has exactly the Cameron--Martin energy `v⁻¹`. -/
theorem integral_sq_firstScore (v : ℝ≥0) :
    ∫ z, firstScore v z ^ 2 ∂gaussianReal 0 v = (v : ℝ)⁻¹ := by
  simp_rw [firstScore, div_pow]
  rw [integral_div, gaussian_second_moment]
  by_cases hv : (v : ℝ) = 0
  · simp [hv]
  · field_simp

/-- An actual Gaussian fourth moment, obtained from its moment generating
function rather than stipulated as a moment hypothesis. -/
theorem gaussian_fourth_moment (v : ℝ≥0) :
    ∫ z : ℝ, z ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  let b : ℝ := v
  let g₀ : ℝ → ℝ := fun t => Real.exp (b * t ^ 2 / 2)
  let g₁ : ℝ → ℝ := fun t => b * t * g₀ t
  let g₂ : ℝ → ℝ := fun t => (b + b ^ 2 * t ^ 2) * g₀ t
  let g₃ : ℝ → ℝ := fun t => (3 * b ^ 2 * t + b ^ 3 * t ^ 3) * g₀ t
  let g₄ : ℝ → ℝ := fun t => (3 * b ^ 2 + 6 * b ^ 3 * t ^ 2 + b ^ 4 * t ^ 4) * g₀ t
  have h₀ (t : ℝ) : HasDerivAt g₀ (g₁ t) t := by
    convert! ((((hasDerivAt_const t b).mul ((hasDerivAt_id t).pow 2)).div_const 2).exp)
      using 1; dsimp [g₀, g₁]; ring
  have h₁ (t : ℝ) : HasDerivAt g₁ (g₂ t) t := by
    convert! (((hasDerivAt_const t b).mul (hasDerivAt_id t)).mul (h₀ t))
      using 1; dsimp [g₁, g₂]; ring
  have h₂ (t : ℝ) : HasDerivAt g₂ (g₃ t) t := by
    convert! ((hasDerivAt_const t b).add
      ((hasDerivAt_const t (b ^ 2)).mul ((hasDerivAt_id t).pow 2))).mul (h₀ t)
      using 1; dsimp [g₂, g₃]; ring
  have h₃ (t : ℝ) : HasDerivAt g₃ (g₄ t) t := by
    convert! ((((hasDerivAt_const t (3 * b ^ 2)).mul (hasDerivAt_id t)).add
      ((hasDerivAt_const t (b ^ 3)).mul ((hasDerivAt_id t).pow 3))).mul (h₀ t))
      using 1; dsimp [g₃, g₄]; ring
  have d₀ : deriv g₀ = g₁ := funext (fun t => (h₀ t).deriv)
  have d₁ : deriv g₁ = g₂ := funext (fun t => (h₁ t).deriv)
  have d₂ : deriv g₂ = g₃ := funext (fun t => (h₂ t).deriv)
  have d₃ : deriv g₃ = g₄ := funext (fun t => (h₃ t).deriv)
  calc
    (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 v) =
        iteratedDeriv 4 (mgf (fun z : ℝ => z) (gaussianReal 0 v)) 0 := by
      rw [iteratedDeriv_mgf_zero] <;> simp
    _ = iteratedDeriv 4 g₀ 0 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, g₀, b]
    _ = g₄ 0 := by
      rw [show 4 = 3 + 1 by rfl, iteratedDeriv_succ', d₀,
        show 3 = 2 + 1 by rfl, iteratedDeriv_succ', d₁,
        show 2 = 1 + 1 by rfl, iteratedDeriv_succ', d₂,
        iteratedDeriv_one, d₃]
    _ = 3 * (v : ℝ) ^ 2 := by simp [g₄, g₀, b]

theorem integrable_secondScore (v : ℝ≥0) :
    Integrable (secondScore v) (gaussianReal 0 v) := by
  have hz : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  change Integrable (fun z : ℝ => (z ^ 2 - (v : ℝ)) / (v : ℝ) ^ 2) (gaussianReal 0 v)
  simpa only [div_eq_mul_inv, Pi.sub_apply] using
    (hz.sub (integrable_const (v : ℝ))).mul_const (((v : ℝ) ^ 2)⁻¹)

/-- Exact zero mean of the old score, including the degenerate convention. -/
theorem integral_secondScore (v : ℝ≥0) :
    ∫ z, secondScore v z ∂gaussianReal 0 v = 0 := by
  have hz : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  rw [show (fun z => secondScore v z) =
      fun z => (z ^ 2 - (v : ℝ)) / (v : ℝ) ^ 2 by rfl,
    integral_div, integral_sub hz (integrable_const _), gaussian_second_moment]
  simp

/-- The old covariance score has exactly the expected square energy.  This
checks its normalized second moment without an assumed score estimate. -/
theorem integral_sq_secondScore (v : ℝ≥0) :
    ∫ z, secondScore v z ^ 2 ∂gaussianReal 0 v = 2 / (v : ℝ) ^ 2 := by
  have hz₂ : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hz₄ : Integrable (fun z : ℝ => z ^ 4) (gaussianReal 0 v) := by
    simpa only [id_eq, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs] using
      (memLp_id_gaussianReal' (μ := 0) (v := v) 4 (by norm_num)).integrable_norm_pow
        (p := 4) (by norm_num)
  have heq : (fun z => secondScore v z ^ 2) =
      fun z => ((z ^ 4 - (2 * (v : ℝ)) * z ^ 2) + (v : ℝ) ^ 2) / (v : ℝ) ^ 4 := by
    ext z
    simp only [secondScore, div_pow]
    ring
  have hdiff : Integrable (fun z : ℝ => z ^ 4 - (2 * (v : ℝ)) * z ^ 2)
      (gaussianReal 0 v) := by
    convert! hz₄.sub (hz₂.const_mul (2 * (v : ℝ))) using 1
  rw [heq, integral_div,
    integral_add hdiff (integrable_const _),
    integral_sub hz₄ (hz₂.const_mul (2 * (v : ℝ))), integral_const_mul,
    gaussian_fourth_moment, gaussian_second_moment]
  simp only [integral_const, probReal_univ, one_smul]
  by_cases hv : (v : ℝ) = 0
  · simp [hv]
  · field_simp
    ring

/-- Every scalar Gaussian polynomial is integrable, with the Gaussian moment
theorem supplying all monomials. -/
theorem integrable_gaussian_power (v : ℝ≥0) (n : ℕ) :
    Integrable (fun z : ℝ => z ^ n) (gaussianReal 0 v) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [norm_pow, id_eq] using
    (memLp_id_gaussianReal' (μ := 0) (v := v) n (by simp)).integrable_norm_pow'
      (p := n)

theorem integrable_gaussian_polynomial (v : ℝ≥0) (P : Polynomial ℝ) :
    Integrable (fun z : ℝ => P.eval z) (gaussianReal 0 v) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert! hP.add hQ using 1
      ext z
      simp only [Polynomial.eval_add, Pi.add_apply]
  | monomial n c =>
      simpa only [Polynomial.eval_monomial] using (integrable_gaussian_power v n).const_mul c

theorem integrable_centered_square_power (v : ℝ≥0) (c : ℝ) (n : ℕ) :
    Integrable (fun z : ℝ => (z ^ 2 - c) ^ n) (gaussianReal 0 v) := by
  convert! integrable_gaussian_polynomial v
    ((Polynomial.X ^ 2 - Polynomial.C c) ^ n) using 1
  ext z
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem integrable_secondScore_power (v : ℝ≥0) (n : ℕ) :
    Integrable (fun z => secondScore v z ^ n) (gaussianReal 0 v) := by
  simpa only [secondScore, div_pow, div_eq_mul_inv, mul_pow, inv_pow] using
    (integrable_centered_square_power v (v : ℝ) n).mul_const (((v : ℝ) ^ 2) ^ n)⁻¹

theorem integrable_firstScore_power (v : ℝ≥0) (n : ℕ) :
    Integrable (fun z => firstScore v z ^ n) (gaussianReal 0 v) := by
  simpa only [firstScore, div_pow, div_eq_mul_inv, mul_pow, inv_pow] using
    (integrable_gaussian_power v n).mul_const (((v : ℝ) ^ n)⁻¹)

/-- Scaling a standard normal by the square root of its target variance gives
the actual variance-v Gaussian, including v=0. -/
theorem gaussian_map_sqrt (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mk, Real.sq_sqrt v.coe_nonneg]

theorem firstScore_scaled {v : ℝ≥0} (hv : v ≠ 0) (z : ℝ) :
    firstScore v (Real.sqrt (v : ℝ) * z) = z / Real.sqrt (v : ℝ) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hs : Real.sqrt (v : ℝ) ≠ 0 := by positivity
  unfold firstScore
  field_simp
  rw [Real.sq_sqrt v.coe_nonneg]
  ring

theorem secondScore_scaled {v : ℝ≥0} (hv : v ≠ 0) (z : ℝ) :
    secondScore v (Real.sqrt (v : ℝ) * z) = (z ^ 2 - 1) / (v : ℝ) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold secondScore
  rw [mul_pow, Real.sq_sqrt v.coe_nonneg]
  field_simp

/-- The even moments of the normalized old second score are independent of
its variance. This supplies every fixed Gaussian moment needed by the
native amplitude truncation, without an assumed moment estimate. -/
theorem secondScore_even_moment_scaling {v : ℝ≥0} (hv : v ≠ 0) (m : ℕ) :
    (∫ z, secondScore v z ^ (2 * m) ∂gaussianReal 0 v) =
      (∫ z : ℝ, (z ^ 2 - 1) ^ (2 * m) ∂gaussianReal 0 1) /
        (v : ℝ) ^ (2 * m) := by
  rw [← gaussian_map_sqrt v, integral_map (by fun_prop) (by unfold secondScore; fun_prop)]
  simp_rw [secondScore_scaled hv, div_pow]
  rw [integral_div]

/-- The same variance-uniform even-moment statement for the new mean score. -/
theorem firstScore_even_moment_scaling {v : ℝ≥0} (hv : v ≠ 0) (m : ℕ) :
    (∫ z, firstScore v z ^ (2 * m) ∂gaussianReal 0 v) =
      (∫ z : ℝ, z ^ (2 * m) ∂gaussianReal 0 1) / (v : ℝ) ^ m := by
  rw [← gaussian_map_sqrt v, integral_map (by fun_prop) (by unfold firstScore; fun_prop)]
  simp_rw [firstScore_scaled hv, div_pow]
  rw [integral_div]
  congr 1
  rw [pow_mul, Real.sq_sqrt v.coe_nonneg]

/-- Standard-normal constants for every fixed even score moment. These are
finite actual polynomial moments, whose integrability was proved above. -/
def firstScoreMoment (m : ℕ) : ℝ := ∫ z : ℝ, z ^ (2 * m) ∂gaussianReal 0 1

def secondScoreMoment (m : ℕ) : ℝ :=
  ∫ z : ℝ, (z ^ 2 - 1) ^ (2 * m) ∂gaussianReal 0 1

theorem firstScoreMoment_nonneg (m : ℕ) : 0 ≤ firstScoreMoment m := by
  apply integral_nonneg
  intro z
  exact (even_two_mul m).pow_nonneg z

theorem secondScoreMoment_nonneg (m : ℕ) : 0 ≤ secondScoreMoment m := by
  apply integral_nonneg
  intro z
  exact (even_two_mul m).pow_nonneg (z ^ 2 - 1)

/-- Variance-uniform high even moments of the normalized covariance score. -/
theorem secondScore_all_fixed_even_moments (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : ℝ≥0), v ≠ 0 →
      Integrable (fun z => |secondScore v z| ^ (2 * m)) (gaussianReal 0 v) ∧
      (∫ z, |secondScore v z| ^ (2 * m) ∂gaussianReal 0 v) =
        C / (v : ℝ) ^ (2 * m) := by
  refine ⟨secondScoreMoment m, secondScoreMoment_nonneg m, ?_⟩
  intro v hv
  simp only [pow_abs_two_mul]
  exact ⟨integrable_secondScore_power v (2 * m), secondScore_even_moment_scaling hv m⟩

/-- Variance-uniform high even moments of the normalized mean score. -/
theorem firstScore_all_fixed_even_moments (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : ℝ≥0), v ≠ 0 →
      Integrable (fun z => |firstScore v z| ^ (2 * m)) (gaussianReal 0 v) ∧
      (∫ z, |firstScore v z| ^ (2 * m) ∂gaussianReal 0 v) =
        C / (v : ℝ) ^ m := by
  refine ⟨firstScoreMoment m, firstScoreMoment_nonneg m, ?_⟩
  intro v hv
  simp only [pow_abs_two_mul]
  exact ⟨integrable_firstScore_power v (2 * m), firstScore_even_moment_scaling hv m⟩

/-- Mixed old-second/new-first score moments on two independent Gaussian
fractions factor exactly, with no assumption on a purported Gaussian moment. -/
theorem independent_mixed_score_even_moment {u v : ℝ≥0}
    (hu : u ≠ 0) (hv : v ≠ 0) (m : ℕ) :
    (∫ w, (∫ z, |firstScore u w * secondScore v z| ^ (2 * m)
        ∂gaussianReal 0 v) ∂gaussianReal 0 u) =
      (firstScoreMoment m / (u : ℝ) ^ m) *
        (secondScoreMoment m / (v : ℝ) ^ (2 * m)) := by
  simp_rw [abs_mul, mul_pow, pow_abs_two_mul]
  simp_rw [integral_const_mul]
  rw [integral_mul_const, firstScore_even_moment_scaling hu m,
    secondScore_even_moment_scaling hv m]
  rfl

/-- Unnormalized even Gaussian moments; this form also includes zero
variance and is convenient for finite-dimensional score directions. -/
theorem gaussian_even_moment (v : ℝ≥0) (m : ℕ) :
    (∫ z : ℝ, z ^ (2 * m) ∂gaussianReal 0 v) =
      (v : ℝ) ^ m * firstScoreMoment m := by
  rw [← gaussian_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [pow_mul, Real.sq_sqrt v.coe_nonneg, integral_const_mul]
  rfl

theorem gaussian_centered_square_even_moment (v : ℝ≥0) (m : ℕ) :
    (∫ z : ℝ, (z ^ 2 - (v : ℝ)) ^ (2 * m) ∂gaussianReal 0 v) =
      (v : ℝ) ^ (2 * m) * secondScoreMoment m := by
  rw [← gaussian_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  have heq (z : ℝ) : (Real.sqrt (v : ℝ) * z) ^ 2 - (v : ℝ) =
      (v : ℝ) * (z ^ 2 - 1) := by
    rw [mul_pow, Real.sq_sqrt v.coe_nonneg]
    ring
  simp_rw [heq, mul_pow]
  rw [integral_const_mul]
  rfl

section GaussianProjections
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ)

/-- Every centered linear projection of the actual Gaussian vector has its
one-dimensional Gaussian law, including singular covariance directions. -/
theorem centered_projection_hasLaw :
    HasLaw (fun x => L x - ∫ y, L y ∂μ)
      (gaussianReal 0 (Var[L; μ]).toNNReal) μ where
  aemeasurable := by fun_prop
  map_eq := by
    have hmap : μ.map (fun x => L x - ∫ y, L y ∂μ) =
        (μ.map L).map (fun z : ℝ => z - ∫ y, L y ∂μ) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [hmap, IsGaussian.map_eq_gaussianReal L, gaussianReal_map_sub_const]
    simp

/-- Actual finite-dimensional Gaussian mean-score moments. Taking
`L=(C⁺d)ᵀ` gives the mean-score energy once its variance is identified. -/
theorem gaussian_projection_even_moment (m : ℕ) :
    Integrable (fun x => |L x - ∫ y, L y ∂μ| ^ (2 * m)) μ ∧
    (∫ x, |L x - ∫ y, L y ∂μ| ^ (2 * m) ∂μ) =
      Var[L; μ] ^ m * firstScoreMoment m := by
  have hLaw := centered_projection_hasLaw μ L
  have hVar : ((Var[L; μ]).toNNReal : ℝ) = Var[L; μ] := by
    simp only [Real.coe_toNNReal', max_eq_left (variance_nonneg L μ)]
  simp only [pow_abs_two_mul]
  constructor
  · simpa only [Function.comp_def] using
      hLaw.integrable_comp (integrable_gaussian_power (Var[L; μ]).toNNReal (2 * m))
  · calc
      (∫ x, (L x - ∫ y, L y ∂μ) ^ (2 * m) ∂μ) =
          ∫ z : ℝ, z ^ (2 * m) ∂gaussianReal 0 (Var[L; μ]).toNNReal := by
        exact hLaw.integral_comp (f := fun z : ℝ => z ^ (2 * m)) (by fun_prop)
      _ = Var[L; μ] ^ m * firstScoreMoment m := by
        rw [gaussian_even_moment, hVar]

/-- Actual rank-one covariance-score moments in every Gaussian dimension.
The direction is encoded by a continuous linear projection, so this includes
singular full covariances without choosing or differentiating a square root. -/
theorem gaussian_projection_covariance_score_even_moment (m : ℕ) :
    Integrable (fun x => |(L x - ∫ y, L y ∂μ) ^ 2 - Var[L; μ]| ^ (2 * m)) μ ∧
    (∫ x, |(L x - ∫ y, L y ∂μ) ^ 2 - Var[L; μ]| ^ (2 * m) ∂μ) =
      Var[L; μ] ^ (2 * m) * secondScoreMoment m := by
  have hLaw := centered_projection_hasLaw μ L
  have hVar : ((Var[L; μ]).toNNReal : ℝ) = Var[L; μ] := by
    simp only [Real.coe_toNNReal', max_eq_left (variance_nonneg L μ)]
  simp only [pow_abs_two_mul]
  constructor
  · simpa only [Function.comp_def, hVar] using
      hLaw.integrable_comp (integrable_centered_square_power
        (Var[L; μ]).toNNReal ((Var[L; μ]).toNNReal : ℝ) (2 * m))
  · calc
      (∫ x, ((L x - ∫ y, L y ∂μ) ^ 2 - Var[L; μ]) ^ (2 * m) ∂μ) =
          ∫ z : ℝ, (z ^ 2 - Var[L; μ]) ^ (2 * m)
            ∂gaussianReal 0 (Var[L; μ]).toNNReal := by
        exact hLaw.integral_comp (f := fun z : ℝ => (z ^ 2 - Var[L; μ]) ^ (2 * m))
          (by fun_prop)
      _ = Var[L; μ] ^ (2 * m) * secondScoreMoment m := by
        simpa only [hVar] using gaussian_centered_square_even_moment (Var[L; μ]).toNNReal m

end GaussianProjections

section GaussianDifferentiation

/-- Exact likelihood ratio for a translation of a fixed-variance normal. -/
def meanTilt (v : ℝ≥0) (t z : ℝ) : ℝ :=
  Real.exp (t * z / (v : ℝ) - t ^ 2 / (2 * (v : ℝ)))

theorem integrable_meanTilt (v : ℝ≥0) (t : ℝ) :
    Integrable (meanTilt v t) (gaussianReal 0 v) := by
  convert! (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (t / (v : ℝ))).const_mul
    (Real.exp (-(t ^ 2) / (2 * (v : ℝ)))) using 1
  ext z
  unfold meanTilt
  rw [← Real.exp_add]
  congr 1
  ring

theorem gaussianPDFReal_mean_tilt (v : ℝ≥0) (hv : v ≠ 0) (t z : ℝ) :
    gaussianPDFReal t v z = gaussianPDFReal 0 v z * meanTilt v t z := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold gaussianPDFReal meanTilt
  simp only [sub_zero]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  field_simp
  ring

/-- Equality of the actual Gaussian mean-translation integral and its fixed
measure likelihood representation, valid for any test function. -/
theorem gaussian_mean_integral_eq_tilt (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (t : ℝ) :
    (∫ z, f z ∂gaussianReal t v) = ∫ z, f z * meanTilt v t z ∂gaussianReal 0 v := by
  rw [integral_gaussianReal_eq_integral_smul (μ := t) hv,
    integral_gaussianReal_eq_integral_smul (μ := 0) hv]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    simp only [smul_eq_mul]
    rw [gaussianPDFReal_mean_tilt v hv]
    ring)

theorem hasDerivAt_meanTilt (v : ℝ≥0) (hv : v ≠ 0) (z t : ℝ) :
    HasDerivAt (fun s => meanTilt v s z)
      (meanTilt v t z * (z - t) / (v : ℝ)) t := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold meanTilt
  convert! (((((hasDerivAt_id t).mul_const z).div_const (v : ℝ)).sub
    (((hasDerivAt_id t).pow 2).div_const (2 * (v : ℝ)))).exp) using 1
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  field_simp
  ring

theorem meanTilt_le_exp_abs (v : ℝ≥0) (hv : v ≠ 0) {t : ℝ} (ht : |t| ≤ 1) (z : ℝ) :
    meanTilt v t z ≤ Real.exp (|z| / (v : ℝ)) := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  apply Real.exp_le_exp.mpr
  have htz : t * z ≤ |z| := by
    calc
      t * z ≤ |t * z| := le_abs_self _
      _ = |t| * |z| := abs_mul _ _
      _ ≤ 1 * |z| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      _ = |z| := one_mul _
  have hd := div_le_div_of_nonneg_right htz hv'.le
  have hsq : 0 ≤ t ^ 2 / (2 * (v : ℝ)) := by positivity
  linarith

def meanTiltDerivativeBound (v : ℝ≥0) (M z : ℝ) : ℝ :=
  M * (|z| + 1) * Real.exp (|z| / (v : ℝ)) / (v : ℝ)

theorem integrable_meanTiltDerivativeBound (v : ℝ≥0) (hv : v ≠ 0) (M : ℝ) :
    Integrable (meanTiltDerivativeBound v M) (gaussianReal 0 v) := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  let a : ℝ := 1 / (v : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hexp : Integrable (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal 0 v) := by
    exact integrable_exp_mul_abs (integrable_exp_mul_gaussianReal a)
      (integrable_exp_mul_gaussianReal (-a))
  have hzexp : Integrable (fun z : ℝ => |z| * Real.exp (a * |z|)) (gaussianReal 0 v) := by
    have h := integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
      (μ := gaussianReal 0 v) (X := fun z : ℝ => z) (v := 0) (t := a + 1) (x := a)
      (by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) (a + 1))
      (by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-(a + 1)))
      ha (by rw [abs_of_nonneg (by linarith)]; linarith) 1
    simpa only [pow_one, zero_mul, zero_add] using h
  convert! (hzexp.add hexp).const_mul (M / (v : ℝ)) using 1
  ext z
  dsimp [meanTiltDerivativeBound, a]
  ring_nf

theorem meanTilt_first_derivative_bound (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ z, |f z| ≤ M)
    {t : ℝ} (ht : |t| ≤ 1) (z : ℝ) :
    ‖f z * meanTilt v t z * (z - t) / (v : ℝ)‖ ≤ meanTiltDerivativeBound v M z := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hzt : |z - t| ≤ |z| + 1 := by
    calc
      |z - t| ≤ |z| + |t| := by simpa only [Real.norm_eq_abs] using norm_sub_le z t
      _ ≤ |z| + 1 := add_le_add (le_refl _) ht
  have htilt := meanTilt_le_exp_abs v hv ht z
  have hpos : 0 < meanTilt v t z := Real.exp_pos _
  simp only [norm_div, norm_mul, Real.norm_eq_abs, abs_of_pos hv', abs_of_pos hpos]
  calc
    |f z| * meanTilt v t z * |z - t| / (v : ℝ) ≤
        M * Real.exp (|z| / (v : ℝ)) * (|z| + 1) / (v : ℝ) := by
      apply div_le_div_of_nonneg_right _ hv'.le
      exact mul_le_mul (mul_le_mul (hf z) htilt hpos.le hM) hzt
        (abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
    _ = meanTiltDerivativeBound v M z := by unfold meanTiltDerivativeBound; ring

/-- Genuine differentiation of a Gaussian mean against a bounded measurable
test. The derivative/integral interchange is proved with an integrable
Gaussian-exponential dominator, and the score formula is not a hypothesis. -/
theorem hasDerivAt_gaussian_mean_integral_zero (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hB : ∀ z, |f z| ≤ M) :
    HasDerivAt (fun t => ∫ z, f z ∂gaussianReal t v)
      (∫ z, f z * firstScore v z ∂gaussianReal 0 v) 0 := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hB 0)
  have hfi : Integrable f (gaussianReal 0 v) :=
    (integrable_const M).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 v) (x₀ := (0 : ℝ)) (s := Metric.ball 0 1)
    (F := fun t z => f z * meanTilt v t z)
    (F' := fun t z => f z * meanTilt v t z * (z - t) / (v : ℝ))
    (bound := meanTiltDerivativeBound v M)
    (Metric.ball_mem_nhds 0 (by norm_num))
    (Filter.Eventually.of_forall (fun t => by unfold meanTilt; fun_prop))
    (by simpa [meanTilt] using hfi)
    (by unfold meanTilt; fun_prop)
    (Filter.Eventually.of_forall (fun z t ht =>
      meanTilt_first_derivative_bound v hv f M hM hB
        (by
          have ht' : |t| < 1 := by
            simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
          exact ht'.le) z))
    (integrable_meanTiltDerivativeBound v hv M)
    (Filter.Eventually.of_forall (fun z t _ => by
      convert! (hasDerivAt_meanTilt v hv z t).const_mul (f z) using 1
      ring))
  have htilt : HasDerivAt (fun t => ∫ z, f z * meanTilt v t z ∂gaussianReal 0 v)
      (∫ z, f z * firstScore v z ∂gaussianReal 0 v) 0 := by
    simpa [meanTilt, firstScore, mul_div_assoc] using h.2
  convert! htilt using 1
  funext t
  exact gaussian_mean_integral_eq_tilt v hv f t

def gaussianConvolution (v : ℝ≥0) (f : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ z, f (m + z) ∂gaussianReal 0 v

theorem gaussian_mean_integral_eq_convolution (v : ℝ≥0)
    (f : ℝ → ℝ) (hf : Measurable f) (m : ℝ) :
    (∫ z, f z ∂gaussianReal m v) = gaussianConvolution v f m := by
  have hmap : (gaussianReal 0 v).map (fun z : ℝ => m + z) = gaussianReal m v := by
    simpa using gaussianReal_map_const_add (μ := 0) (v := v) m
  rw [← hmap, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rfl

/-- The physical Gaussian mean score for bounded rough tests, at every mean.
No derivative of the rough test is required. -/
theorem hasDerivAt_gaussianConvolution (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hB : ∀ z, |f z| ≤ M) (m : ℝ) :
    HasDerivAt (gaussianConvolution v f)
      (∫ z, f (m + z) * firstScore v z ∂gaussianReal 0 v) m := by
  have hfm : Measurable (fun z => f (m + z)) := by fun_prop
  have h := hasDerivAt_gaussian_mean_integral_zero v hv (fun z => f (m + z)) hfm M
    (fun z => hB (m + z))
  have hshift : HasDerivAt (fun t => gaussianConvolution v f (m + t))
      (∫ z, f (m + z) * firstScore v z ∂gaussianReal 0 v) 0 := by
    convert! h using 1
    funext t
    rw [gaussian_mean_integral_eq_convolution v (fun z => f (m + z)) hfm t]
    unfold gaussianConvolution
    congr 1
    funext z
    congr 1
    ring
  have hshift' : HasDerivAt (fun t => gaussianConvolution v f (m + t))
      (∫ z, f (m + z) * firstScore v z ∂gaussianReal 0 v) (m - m) := by
    simpa only [sub_self] using hshift
  have hh := hshift'.comp (h := fun x : ℝ => x - m) m ((hasDerivAt_id m).sub_const m)
  have hEq : ((fun t => gaussianConvolution v f (m + t)) ∘ fun x : ℝ => x - m) =
      gaussianConvolution v f := by
    funext x
    dsimp only [Function.comp_def]
    congr 1
    ring
  rw [hEq] at hh
  simpa only [mul_one] using hh

theorem integrable_gaussian_abs_power_exp (v : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Integrable (fun z : ℝ => |z| ^ n * Real.exp (a * |z|)) (gaussianReal 0 v) := by
  have h := integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
    (μ := gaussianReal 0 v) (X := fun z : ℝ => z) (v := 0) (t := a + 1) (x := a)
    (by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) (a + 1))
    (by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-(a + 1)))
    ha (by rw [abs_of_nonneg (by linarith)]; linarith) n
  simpa only [zero_mul, zero_add] using h

def meanTiltSecondDerivativeBound (v : ℝ≥0) (M z : ℝ) : ℝ :=
  M * ((|z| + 1) ^ 2 + (v : ℝ)) * Real.exp (|z| / (v : ℝ)) / (v : ℝ) ^ 2

theorem integrable_meanTiltSecondDerivativeBound (v : ℝ≥0) (hv : v ≠ 0) (M : ℝ) :
    Integrable (meanTiltSecondDerivativeBound v M) (gaussianReal 0 v) := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  let a : ℝ := 1 / (v : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h₀ := integrable_gaussian_abs_power_exp v a ha 0
  have h₁ := integrable_gaussian_abs_power_exp v a ha 1
  have h₂ := integrable_gaussian_abs_power_exp v a ha 2
  convert! ((h₂.add (h₁.const_mul 2)).add (h₀.const_mul (1 + (v : ℝ)))).const_mul
    (M / (v : ℝ) ^ 2) using 1
  ext z
  dsimp [meanTiltSecondDerivativeBound, a]
  simp only [pow_zero, one_mul, pow_one]
  ring_nf

theorem hasDerivAt_meanTilt_first_derivative (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (z t : ℝ) :
    HasDerivAt (fun s => f z * meanTilt v s z * (z - s) / (v : ℝ))
      (f z * meanTilt v t z * secondScore v (z - t)) t := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  convert! (((hasDerivAt_meanTilt v hv z t).const_mul (f z)).mul
    (((hasDerivAt_const t z).sub (hasDerivAt_id t)).div_const (v : ℝ))) using 1
  · funext s
    dsimp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    ring
  · unfold secondScore
    simp only [Pi.sub_apply, id_eq]
    field_simp
    ring

theorem meanTilt_second_derivative_bound (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ z, |f z| ≤ M)
    {t : ℝ} (ht : |t| ≤ 1) (z : ℝ) :
    ‖f z * meanTilt v t z * secondScore v (z - t)‖ ≤
      meanTiltSecondDerivativeBound v M z := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hzt : |z - t| ≤ |z| + 1 := by
    calc
      |z - t| ≤ |z| + |t| := by simpa only [Real.norm_eq_abs] using norm_sub_le z t
      _ ≤ |z| + 1 := add_le_add (le_refl _) ht
  have hsq : (z - t) ^ 2 ≤ (|z| + 1) ^ 2 := by
    rw [← sq_abs (z - t)]
    gcongr
  have hsub : |(z - t) ^ 2 - (v : ℝ)| ≤ (|z| + 1) ^ 2 + (v : ℝ) := by
    calc
      |(z - t) ^ 2 - (v : ℝ)| ≤ |(z - t) ^ 2| + |(v : ℝ)| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le ((z - t) ^ 2) (v : ℝ)
      _ = (z - t) ^ 2 + (v : ℝ) := by rw [abs_of_nonneg (sq_nonneg _), abs_of_pos hv']
      _ ≤ (|z| + 1) ^ 2 + (v : ℝ) := add_le_add hsq (le_refl _)
  have htilt := meanTilt_le_exp_abs v hv ht z
  have hpos : 0 < meanTilt v t z := Real.exp_pos _
  unfold secondScore
  simp only [norm_div, norm_mul, Real.norm_eq_abs, abs_of_pos hv', abs_of_pos hpos,
    abs_pow]
  calc
    |f z| * meanTilt v t z * (|(z - t) ^ 2 - (v : ℝ)| / (v : ℝ) ^ 2) ≤
        M * Real.exp (|z| / (v : ℝ)) *
          (((|z| + 1) ^ 2 + (v : ℝ)) / (v : ℝ) ^ 2) := by
      exact mul_le_mul (mul_le_mul (hf z) htilt hpos.le hM)
        (div_le_div_of_nonneg_right hsub (sq_nonneg _)) (by positivity)
        (mul_nonneg hM (Real.exp_pos _).le)
    _ = meanTiltSecondDerivativeBound v M z := by
      unfold meanTiltSecondDerivativeBound
      ring

/-- A second dominated derivative of the actual mean likelihood integral.
The rough test is still only bounded and measurable. -/
theorem hasDerivAt_gaussian_tilt_gradient_zero (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hB : ∀ z, |f z| ≤ M) :
    HasDerivAt (fun t => ∫ z, f z * meanTilt v t z * (z - t) / (v : ℝ)
        ∂gaussianReal 0 v)
      (∫ z, f z * secondScore v z ∂gaussianReal 0 v) 0 := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hB 0)
  have hfi : Integrable (fun z => f z * firstScore v z) (gaussianReal 0 v) :=
    (integrable_firstScore v).bdd_mul hf.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB z))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 v) (x₀ := (0 : ℝ)) (s := Metric.ball 0 1)
    (F := fun t z => f z * meanTilt v t z * (z - t) / (v : ℝ))
    (F' := fun t z => f z * meanTilt v t z * secondScore v (z - t))
    (bound := meanTiltSecondDerivativeBound v M)
    (Metric.ball_mem_nhds 0 (by norm_num))
    (Filter.Eventually.of_forall (fun t => by unfold meanTilt; fun_prop))
    (by simpa [meanTilt, firstScore, mul_div_assoc] using hfi)
    (by unfold meanTilt secondScore; fun_prop)
    (Filter.Eventually.of_forall (fun z t ht =>
      meanTilt_second_derivative_bound v hv f M hM hB
        (by
          have ht' : |t| < 1 := by
            simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
          exact ht'.le) z))
    (integrable_meanTiltSecondDerivativeBound v hv M)
    (Filter.Eventually.of_forall (fun z t _ =>
      hasDerivAt_meanTilt_first_derivative v hv f z t))
  simpa [meanTilt] using h.2

def gaussianGradient (v : ℝ≥0) (f : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ z, f (m + z) * firstScore v z ∂gaussianReal 0 v

theorem gaussianGradient_shift_eq_tilt (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (m t : ℝ) :
    gaussianGradient v f (m + t) =
      ∫ z, f (m + z) * meanTilt v t z * (z - t) / (v : ℝ) ∂gaussianReal 0 v := by
  let g : ℝ → ℝ := fun z => f (m + z) * (z - t) / (v : ℝ)
  have hg : Measurable g := by dsimp [g]; fun_prop
  calc
    gaussianGradient v f (m + t) = gaussianConvolution v g t := by
      unfold gaussianGradient gaussianConvolution firstScore
      congr 1
      funext z
      dsimp [g]
      have ha : m + (t + z) = m + t + z := by ring
      rw [ha, add_sub_cancel_left]
      ring
    _ = ∫ z, g z ∂gaussianReal t v := (gaussian_mean_integral_eq_convolution v g hg t).symm
    _ = ∫ z, g z * meanTilt v t z ∂gaussianReal 0 v :=
      gaussian_mean_integral_eq_tilt v hv g t
    _ = ∫ z, f (m + z) * meanTilt v t z * (z - t) / (v : ℝ) ∂gaussianReal 0 v := by
      congr 1
      funext z
      dsimp [g]
      ring

/-- Actual second-mean-score differentiation, valid for bounded rough tests. -/
theorem hasDerivAt_gaussianGradient (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hB : ∀ z, |f z| ≤ M) (m : ℝ) :
    HasDerivAt (gaussianGradient v f)
      (∫ z, f (m + z) * secondScore v z ∂gaussianReal 0 v) m := by
  have hfm : Measurable (fun z => f (m + z)) := by fun_prop
  have h := hasDerivAt_gaussian_tilt_gradient_zero v hv (fun z => f (m + z)) hfm M
    (fun z => hB (m + z))
  have hshift : HasDerivAt (fun t => gaussianGradient v f (m + t))
      (∫ z, f (m + z) * secondScore v z ∂gaussianReal 0 v) (m - m) := by
    convert! h using 1
    · funext t
      exact gaussianGradient_shift_eq_tilt v hv f hf m t
    · simp
  have hh := hshift.comp (h := fun x : ℝ => x - m) m ((hasDerivAt_id m).sub_const m)
  have hEq : ((fun t => gaussianGradient v f (m + t)) ∘ fun x : ℝ => x - m) =
      gaussianGradient v f := by
    funext x
    dsimp only [Function.comp_def]
    congr 1
    ring
  rw [hEq] at hh
  simpa only [mul_one] using hh

theorem deriv_gaussianConvolution (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hB : ∀ z, |f z| ≤ M) :
    deriv (gaussianConvolution v f) = gaussianGradient v f := by
  funext m
  exact (hasDerivAt_gaussianConvolution v hv f hf M hB m).deriv

/-- The true second derivative of a Gaussian convolution is its covariance
Hermite score integral. This discharges the scalar n=1 score-transfer step. -/
theorem hasDerivAt_deriv_gaussianConvolution (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hB : ∀ z, |f z| ≤ M) (m : ℝ) :
    HasDerivAt (deriv (gaussianConvolution v f))
      (∫ z, f (m + z) * secondScore v z ∂gaussianReal 0 v) m := by
  rw [deriv_gaussianConvolution v hv f hf M hB]
  exact hasDerivAt_gaussianGradient v hv f hf M hB m

/-- The Gaussian density with a real variance parameter; used only locally
where that parameter is strictly positive. -/
def varianceDensity (w z : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * w))⁻¹ * Real.exp (-z ^ 2 / (2 * w))

theorem varianceDensity_eq_pdf {w : ℝ} (hw : 0 < w) (z : ℝ) :
    varianceDensity w z = gaussianPDFReal 0 w.toNNReal z := by
  simp only [varianceDensity, gaussianPDFReal, Real.coe_toNNReal',
    max_eq_left hw.le, sub_zero]

theorem varianceDensity_pos {w : ℝ} (hw : 0 < w) (z : ℝ) :
    0 < varianceDensity w z := by
  unfold varianceDensity
  positivity

theorem hasDerivAt_varianceDensity {w : ℝ} (hw : 0 < w) (z : ℝ) :
    HasDerivAt (fun t => varianceDensity t z)
      (varianceDensity w z * (z ^ 2 - w) / (2 * w ^ 2)) w := by
  have hroot : Real.sqrt (2 * Real.pi * w) ≠ 0 := by positivity
  have hr : Real.sqrt (2 * Real.pi * w) ^ 2 = 2 * Real.pi * w :=
    Real.sq_sqrt (by positivity)
  have hr₃ : Real.sqrt (2 * Real.pi * w) ^ 3 =
      (2 * Real.pi * w) * Real.sqrt (2 * Real.pi * w) := by
    calc
      _ = Real.sqrt (2 * Real.pi * w) ^ 2 * Real.sqrt (2 * Real.pi * w) := by ring
      _ = _ := by rw [hr]
  have hp : HasDerivAt (fun t : ℝ => (Real.sqrt (2 * Real.pi * t))⁻¹)
      (-(Real.sqrt (2 * Real.pi * w))⁻¹ / (2 * w)) w := by
    convert! (((hasDerivAt_id w).const_mul (2 * Real.pi)).sqrt
      (by simpa only [id_eq] using (show 2 * Real.pi * w ≠ 0 by positivity))).inv hroot
      using 1
    simp only [id_eq]
    field_simp
    nlinarith [hr₃]
  have he : HasDerivAt (fun t : ℝ => Real.exp (-z ^ 2 / (2 * t)))
      (Real.exp (-z ^ 2 / (2 * w)) * z ^ 2 / (2 * w ^ 2)) w := by
    have hd : HasDerivAt (fun t : ℝ => 2 * t) 2 w := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id w).const_mul 2
    convert! ((hasDerivAt_const w (-z ^ 2)).div ((hasDerivAt_id w).const_mul 2)
      (by simpa only [id_eq, mul_comm] using (show 2 * w ≠ 0 by positivity))).exp using 1
    simp only [Pi.div_apply, id_eq]
    field_simp
    ring
  convert! hp.mul he using 1
  unfold varianceDensity
  field_simp
  ring

theorem varianceDensity_le_broader {v w : ℝ} (hv : 0 < v)
    (hw : v / 2 ≤ w) (hw₂ : w ≤ 2 * v) (z : ℝ) :
    varianceDensity w z ≤ 2 * varianceDensity (2 * v) z := by
  have hwpos : 0 < w := by linarith
  have hA : 0 < Real.sqrt (2 * Real.pi * w) := by positivity
  have hB : 0 < Real.sqrt (2 * Real.pi * (2 * v)) := by positivity
  have hsA := Real.sq_sqrt (show 0 ≤ 2 * Real.pi * w by positivity)
  have hsB := Real.sq_sqrt (show 0 ≤ 2 * Real.pi * (2 * v) by positivity)
  have hroot : Real.sqrt (2 * Real.pi * (2 * v)) ≤
      2 * Real.sqrt (2 * Real.pi * w) := by nlinarith [Real.pi_pos]
  have hpre : (Real.sqrt (2 * Real.pi * w))⁻¹ ≤
      2 * (Real.sqrt (2 * Real.pi * (2 * v)))⁻¹ := by
    have h : 1 / (Real.sqrt (2 * Real.pi * w)) ≤
        2 / (Real.sqrt (2 * Real.pi * (2 * v))) :=
      (div_le_div_iff₀ hA hB).mpr (by simpa using hroot)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hexp : Real.exp (-z ^ 2 / (2 * w)) ≤
      Real.exp (-z ^ 2 / (2 * (2 * v))) := by
    apply Real.exp_le_exp.mpr
    have h : z ^ 2 / (2 * (2 * v)) ≤ z ^ 2 / (2 * w) :=
      div_le_div_of_nonneg_left (sq_nonneg z) (by positivity) (by linarith)
    simpa only [neg_div] using neg_le_neg h
  unfold varianceDensity
  calc
    (Real.sqrt (2 * Real.pi * w))⁻¹ * Real.exp (-z ^ 2 / (2 * w)) ≤
        (2 * (Real.sqrt (2 * Real.pi * (2 * v)))⁻¹) *
          Real.exp (-z ^ 2 / (2 * (2 * v))) := by
      exact mul_le_mul hpre hexp (Real.exp_pos _).le (by positivity)
    _ = 2 * ((Real.sqrt (2 * Real.pi * (2 * v)))⁻¹ *
        Real.exp (-z ^ 2 / (2 * (2 * v)))) := by ring

theorem integrable_gaussian_density_mul (v : ℝ≥0) (hv : v ≠ 0)
    (g : ℝ → ℝ) (hg : Integrable g (gaussianReal 0 v)) :
    Integrable (fun z => gaussianPDFReal 0 v z * g z) volume := by
  rw [gaussianReal_of_var_ne_zero 0 hv] at hg
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 v)
    (Filter.Eventually.of_forall (fun z =>
      (show gaussianPDF 0 v z < ∞ from gaussianPDF_lt_top)))).mp hg
  convert! h using 1
  ext z
  rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v z)]
  rfl

theorem integrable_varianceDensity_mul (w : ℝ) (hw : 0 < w)
    (g : ℝ → ℝ) (hg : Integrable g (gaussianReal 0 w.toNNReal)) :
    Integrable (fun z => varianceDensity w z * g z) volume := by
  simp_rw [varianceDensity_eq_pdf hw]
  exact integrable_gaussian_density_mul w.toNNReal (by positivity) g hg

def varianceDerivativeBound (v M z : ℝ) : ℝ :=
  (4 * M / v ^ 2) * (z ^ 2 + 2 * v) * varianceDensity (2 * v) z

theorem integrable_varianceDerivativeBound (v : ℝ) (hv : 0 < v) (M : ℝ) :
    Integrable (varianceDerivativeBound v M) volume := by
  have hg : Integrable (fun z : ℝ => z ^ 2 + 2 * v)
      (gaussianReal 0 (2 * v).toNNReal) := by
    convert! (integrable_gaussian_power (2 * v).toNNReal 2).add (integrable_const (2 * v)) using 1
  have hd := integrable_varianceDensity_mul (2 * v) (by positivity)
    (fun z : ℝ => z ^ 2 + 2 * v) hg
  convert! hd.const_mul (4 * M / v ^ 2) using 1
  ext z
  unfold varianceDerivativeBound
  ring

theorem varianceDensity_derivative_bound {v w : ℝ} (hv : 0 < v)
    (hw : v / 2 ≤ w) (hw₂ : w ≤ 2 * v)
    (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ z, |f z| ≤ M) (z : ℝ) :
    ‖f z * varianceDensity w z * (z ^ 2 - w) / (2 * w ^ 2)‖ ≤
      varianceDerivativeBound v M z := by
  have hwpos : 0 < w := by linarith
  have hdpos := varianceDensity_pos hwpos z
  have hbpos := varianceDensity_pos (show 0 < 2 * v by positivity) z
  have hsub : |z ^ 2 - w| ≤ z ^ 2 + 2 * v := by
    calc
      |z ^ 2 - w| ≤ |z ^ 2| + |w| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (z ^ 2) w
      _ = z ^ 2 + w := by rw [abs_of_nonneg (sq_nonneg _), abs_of_pos hwpos]
      _ ≤ z ^ 2 + 2 * v := add_le_add (le_refl _) hw₂
  have hden : v ^ 2 / 2 ≤ 2 * w ^ 2 := by
    have hs : (v / 2) ^ 2 ≤ w ^ 2 := by gcongr
    nlinarith
  have hratio : |z ^ 2 - w| / (2 * w ^ 2) ≤ 2 * (z ^ 2 + 2 * v) / v ^ 2 := by
    calc
      _ ≤ (z ^ 2 + 2 * v) / (2 * w ^ 2) :=
        div_le_div_of_nonneg_right hsub (by positivity)
      _ ≤ (z ^ 2 + 2 * v) / (v ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by ring
  have hd := varianceDensity_le_broader hv hw hw₂ z
  simp only [norm_div, norm_mul, Real.norm_eq_abs, abs_of_pos hdpos,
    abs_of_pos (show 0 < (2 : ℝ) by norm_num), abs_of_nonneg (sq_nonneg w)]
  calc
    |f z| * varianceDensity w z * |z ^ 2 - w| / (2 * w ^ 2) =
        (|f z| * varianceDensity w z) * (|z ^ 2 - w| / (2 * w ^ 2)) := by ring
    _ ≤ (M * (2 * varianceDensity (2 * v) z)) *
        (2 * (z ^ 2 + 2 * v) / v ^ 2) := by
      exact mul_le_mul (mul_le_mul (hf z) hd hdpos.le hM) hratio (by positivity)
        (mul_nonneg hM (mul_nonneg (by norm_num) hbpos.le))
    _ = varianceDerivativeBound v M z := by unfold varianceDerivativeBound; ring

/-- Genuine covariance-parameter differentiation against bounded measurable
rough tests. The density derivative is dominated by a polynomial times a
broader Gaussian density, whose integrability is proved from actual moments. -/
theorem hasDerivAt_gaussian_variance_integral (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hB : ∀ z, |f z| ≤ M) :
    HasDerivAt (fun w : ℝ => ∫ z, f z ∂gaussianReal 0 w.toNNReal)
      ((1 / 2 : ℝ) * ∫ z, f z * secondScore v z ∂gaussianReal 0 v) (v : ℝ) := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hB 0)
  have hfi : Integrable f (gaussianReal 0 v) :=
    (integrable_const M).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hFint : Integrable (fun z => f z * varianceDensity (v : ℝ) z) volume := by
    convert! integrable_gaussian_density_mul v hv f hfi using 1
    funext z
    rw [varianceDensity_eq_pdf hv', Real.toNNReal_coe]
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (x₀ := (v : ℝ))
    (s := Metric.ball (v : ℝ) ((v : ℝ) / 2))
    (F := fun w z => f z * varianceDensity w z)
    (F' := fun w z => f z * varianceDensity w z * (z ^ 2 - w) / (2 * w ^ 2))
    (bound := varianceDerivativeBound (v : ℝ) M)
    (Metric.ball_mem_nhds (v : ℝ) (by positivity))
    (Filter.Eventually.of_forall (fun w => by unfold varianceDensity; fun_prop)) hFint
    (by unfold varianceDensity; fun_prop)
    (Filter.Eventually.of_forall (fun z w hw => by
      have hb : |w - (v : ℝ)| < (v : ℝ) / 2 := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hw
      rcases abs_lt.mp hb with ⟨hl, hu⟩
      exact varianceDensity_derivative_bound hv' (by linarith) (by linarith)
        f M hM hB z))
    (integrable_varianceDerivativeBound (v : ℝ) hv' M)
    (Filter.Eventually.of_forall (fun z w hw => by
      have hb : |w - (v : ℝ)| < (v : ℝ) / 2 := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hw
      have hw' : 0 < w := by have hh := abs_lt.mp hb; linarith
      convert! (hasDerivAt_varianceDensity hw' z).const_mul (f z) using 1
      ring))
  have hcoeff :
      (∫ z, f z * varianceDensity (v : ℝ) z * (z ^ 2 - (v : ℝ)) /
          (2 * (v : ℝ) ^ 2)) =
        (1 / 2 : ℝ) * ∫ z, f z * secondScore v z ∂gaussianReal 0 v := by
    rw [integral_gaussianReal_eq_integral_smul hv, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only
      rw [varianceDensity_eq_pdf hv', Real.toNNReal_coe]
      simp only [smul_eq_mul, secondScore]
      ring)
  rw [hcoeff] at h
  apply h.2.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hv'] with w hw
  change 0 < w at hw
  rw [integral_gaussianReal_eq_integral_smul (v := w.toNNReal) (by positivity)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [varianceDensity_eq_pdf hw]
    simp only [smul_eq_mul]
    ring)

end GaussianDifferentiation

section RankOneGaussianFamilies
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def rankOneAdd (d : E) : E × ℝ →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E ℝ) + (ContinuousLinearMap.snd ℝ E ℝ).smulRight d

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem rankOneAdd_apply (d : E) (x : E) (z : ℝ) :
    rankOneAdd d (x, z) = x + z • d := by simp [rankOneAdd]

/-- A real Gaussian rank-one covariance fraction added to a residual law. -/
def rankOneGaussianLaw (ν : Measure E) (d : E) (v : ℝ≥0) : Measure E :=
  (ν.prod (gaussianReal 0 v)).map (rankOneAdd d)

instance rankOneGaussianLaw_isProbabilityMeasure (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (v : ℝ≥0) : IsProbabilityMeasure (rankOneGaussianLaw ν d v) := by
  unfold rankOneGaussianLaw
  infer_instance

instance rankOneGaussianLaw_isGaussian (ν : Measure E) [IsGaussian ν] (d : E) (v : ℝ≥0) :
    IsGaussian (rankOneGaussianLaw ν d v) := by
  unfold rankOneGaussianLaw
  infer_instance

def rankOneAverage (ν : Measure E) (d : E) (F : E → ℝ) (z : ℝ) : ℝ :=
  ∫ x, F (x + z • d) ∂ν

theorem measurable_rankOneAverage (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (F : E → ℝ) (hF : Measurable F) : Measurable (rankOneAverage ν d F) := by
  have h : Measurable (fun p : ℝ × E => F (p.2 + p.1 • d)) := by fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

omit [BorelSpace E] [SecondCountableTopology E] in
theorem rankOneAverage_bound (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (F : E → ℝ) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (z : ℝ) :
    |rankOneAverage ν d F z| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x => F (x + z • d)) (C := M)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB (x + z • d)))
  simpa only [rankOneAverage, Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- Fubini identifies the genuine output-law expectation with a scalar
Gaussian expectation of the residual average; no covariance inverse appears. -/
theorem integral_rankOneGaussianLaw (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (v : ℝ≥0) (F : E → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    (∫ y, F y ∂rankOneGaussianLaw ν d v) =
      ∫ z, rankOneAverage ν d F z ∂gaussianReal 0 v := by
  have hp : Integrable (fun p : E × ℝ => F (rankOneAdd d p))
      (ν.prod (gaussianReal 0 v)) :=
    (integrable_const M).mono' (hF.comp (rankOneAdd d).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hB _))
  rw [rankOneGaussianLaw, integral_map (by fun_prop) hF.aestronglyMeasurable,
    integral_prod_symm _ hp]
  simp only [rankOneAverage, rankOneAdd_apply]

/-- Recovering the reserved scalar fraction by a linear functional identifies
its Hermite score as an actual score on the output Gaussian law. -/
theorem rankOne_score_integral (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (v : ℝ≥0) (F : E → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) (L : E →L[ℝ] ℝ)
    (hLd : L d = 1) (hker : ∀ᵐ x ∂ν, L x = 0)
    (S : ℝ → ℝ) (hS : Measurable S) (hSint : Integrable S (gaussianReal 0 v)) :
    (∫ y, F y * S (L y) ∂rankOneGaussianLaw ν d v) =
      ∫ z, rankOneAverage ν d F z * S z ∂gaussianReal 0 v := by
  have hp : Integrable (fun p : E × ℝ => F (rankOneAdd d p) * S p.2)
      (ν.prod (gaussianReal 0 v)) :=
    (hSint.comp_snd ν).bdd_mul (hF.comp (rankOneAdd d).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hB _))
  have hk : ∀ᵐ p ∂ν.prod (gaussianReal 0 v), L p.1 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae hker
  rw [rankOneGaussianLaw, integral_map (by fun_prop) (by fun_prop)]
  calc
    (∫ p : E × ℝ, F (rankOneAdd d p) * S (L (rankOneAdd d p))
        ∂ν.prod (gaussianReal 0 v)) =
        ∫ p : E × ℝ, F (rankOneAdd d p) * S p.2 ∂ν.prod (gaussianReal 0 v) := by
      apply integral_congr_ae
      filter_upwards [hk] with p hp
      rcases p with ⟨x, z⟩
      dsimp only at hp
      simp only [rankOneAdd_apply, map_add, map_smul, hp, hLd,
        smul_eq_mul, mul_one, zero_add]
    _ = ∫ z, ∫ x, F (rankOneAdd d (x, z)) * S z ∂ν ∂gaussianReal 0 v :=
      integral_prod_symm _ hp
    _ = ∫ z, rankOneAverage ν d F z * S z ∂gaussianReal 0 v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        dsimp only
        rw [integral_mul_const]
        simp only [rankOneAverage, rankOneAdd_apply])

omit [SecondCountableTopology E] in
/-- An exact Gaussian range coordinate of the output law. A singular residual
is permitted: only its support in the kernel of the coordinate is required. -/
theorem rankOne_projection_hasLaw (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (v : ℝ≥0) (L : E →L[ℝ] ℝ) (hLd : L d = 1)
    (hker : ∀ᵐ x ∂ν, L x = 0) :
    HasLaw L (gaussianReal 0 v) (rankOneGaussianLaw ν d v) where
  aemeasurable := by fun_prop
  map_eq := by
    rw [rankOneGaussianLaw, Measure.map_map (by fun_prop) (by fun_prop)]
    have hk : ∀ᵐ p ∂ν.prod (gaussianReal 0 v), L p.1 = 0 :=
      Measure.quasiMeasurePreserving_fst.ae hker
    have heq : (L ∘ rankOneAdd d) =ᵐ[ν.prod (gaussianReal 0 v)] Prod.snd := by
      filter_upwards [hk] with p hp
      rcases p with ⟨x, z⟩
      dsimp only [Function.comp_def] at hp ⊢
      simp only [rankOneAdd_apply, map_add, map_smul, hp, hLd,
        smul_eq_mul, mul_one, zero_add]
    rw [Measure.map_congr heq]
    exact measurePreserving_snd.map_eq

omit [BorelSpace E] [SecondCountableTopology E] in
theorem rankOneAverage_shift (ν : Measure E) (d : E) (F : E → ℝ) (m z : ℝ) :
    rankOneAverage ν d (fun y => F (y + m • d)) z = rankOneAverage ν d F (m + z) := by
  unfold rankOneAverage
  congr 1
  funext x
  have he : (x + z • d) + m • d = x + (m + z) • d := by
    rw [add_smul]
    abel
  exact congrArg F he

def rankOneMeanExpectation (ν : Measure E) (d : E) (v : ℝ≥0) (F : E → ℝ) (m : ℝ) : ℝ :=
  ∫ y, F (y + m • d) ∂rankOneGaussianLaw ν d v

theorem rankOneMeanExpectation_eq_convolution (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (v : ℝ≥0) (F : E → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    rankOneMeanExpectation ν d v F = gaussianConvolution v (rankOneAverage ν d F) := by
  funext m
  unfold rankOneMeanExpectation
  rw [integral_rankOneGaussianLaw ν d v (fun y => F (y + m • d)) (by fun_prop) M
    (fun y => hB _)]
  simp_rw [rankOneAverage_shift]
  rfl

/-- Genuine finite-dimensional rank-one mean-score differentiation on the
output Gaussian law, including singular covariance in complementary directions. -/
theorem hasDerivAt_rankOneMeanExpectation (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (v : ℝ≥0) (hv : v ≠ 0) (F : E → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) (L : E →L[ℝ] ℝ)
    (hLd : L d = 1) (hker : ∀ᵐ x ∂ν, L x = 0) (m : ℝ) :
    HasDerivAt (rankOneMeanExpectation ν d v F)
      (∫ y, F (y + m • d) * firstScore v (L y) ∂rankOneGaussianLaw ν d v) m := by
  have hscore := rankOne_score_integral ν d v (fun y => F (y + m • d)) (by fun_prop)
    M (fun y => hB _) L hLd hker (firstScore v)
    (by unfold firstScore; fun_prop) (integrable_firstScore v)
  simp_rw [rankOneAverage_shift] at hscore
  rw [rankOneMeanExpectation_eq_convolution ν d v F hF M hB, hscore]
  exact hasDerivAt_gaussianConvolution v hv (rankOneAverage ν d F)
    (measurable_rankOneAverage ν d F hF) M (rankOneAverage_bound ν d F M hB) m

/-- The actual second directional mean derivative has the actual rank-one
covariance Hermite score. No inverse covariance is differentiated. -/
theorem hasDerivAt_deriv_rankOneMeanExpectation (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (v : ℝ≥0) (hv : v ≠ 0) (F : E → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) (L : E →L[ℝ] ℝ)
    (hLd : L d = 1) (hker : ∀ᵐ x ∂ν, L x = 0) (m : ℝ) :
    HasDerivAt (deriv (rankOneMeanExpectation ν d v F))
      (∫ y, F (y + m • d) * secondScore v (L y) ∂rankOneGaussianLaw ν d v) m := by
  have hscore := rankOne_score_integral ν d v (fun y => F (y + m • d)) (by fun_prop)
    M (fun y => hB _) L hLd hker (secondScore v)
    (by unfold secondScore; fun_prop) (integrable_secondScore v)
  simp_rw [rankOneAverage_shift] at hscore
  rw [rankOneMeanExpectation_eq_convolution ν d v F hF M hB, hscore]
  exact hasDerivAt_deriv_gaussianConvolution v hv (rankOneAverage ν d F)
    (measurable_rankOneAverage ν d F hF) M (rankOneAverage_bound ν d F M hB) m

/-- The covariance derivative of the actual rank-one Gaussian output family.
The reserve coordinate gives an exact formula uniformly over conditioning
of every complementary covariance direction. -/
theorem hasDerivAt_rankOne_variance (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) (v : ℝ≥0) (hv : v ≠ 0) (F : E → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) (L : E →L[ℝ] ℝ)
    (hLd : L d = 1) (hker : ∀ᵐ x ∂ν, L x = 0) :
    HasDerivAt (fun w : ℝ => ∫ y, F y ∂rankOneGaussianLaw ν d w.toNNReal)
      ((1 / 2 : ℝ) * ∫ y, F y * secondScore v (L y) ∂rankOneGaussianLaw ν d v)
      (v : ℝ) := by
  have h := hasDerivAt_gaussian_variance_integral v hv (rankOneAverage ν d F)
    (measurable_rankOneAverage ν d F hF) M (rankOneAverage_bound ν d F M hB)
  have hscore := rankOne_score_integral ν d v F hF M hB L hLd hker (secondScore v)
    (by unfold secondScore; fun_prop) (integrable_secondScore v)
  convert! h using 1
  · funext w
    exact integral_rankOneGaussianLaw ν d w.toNNReal F hF M hB
  · rw [hscore]

omit [SecondCountableTopology E] in
/-- The scalar reserve changes the actual output covariance by precisely the
rank-one form `v (K d)^2`, independently of degeneracy in the residual law. -/
theorem variance_rankOneGaussianLaw [CompleteSpace E]
    (ν : Measure E) [IsGaussian ν] (d : E) (v : ℝ≥0) (K : E →L[ℝ] ℝ) :
    Var[K; rankOneGaussianLaw ν d v] = Var[K; ν] + (v : ℝ) * (K d) ^ 2 := by
  unfold rankOneGaussianLaw
  rw [variance_map (by fun_prop) (by fun_prop)]
  have heq : (K ∘ rankOneAdd d) = fun p : E × ℝ => K p.1 + K d * p.2 := by
    funext ⟨x, z⟩
    simp only [Function.comp_def, rankOneAdd_apply, map_add, map_smul, smul_eq_mul]
    ring
  have hz₂ : MemLp (fun z : ℝ => K d * z) 2 (gaussianReal 0 v) := by
    simpa only [ContinuousLinearMap.id_apply] using
      (IsGaussian.memLp_dual (gaussianReal 0 v) (ContinuousLinearMap.id ℝ ℝ) 2
        (by norm_num)).const_mul (K d)
  rw [heq, variance_add_prod (IsGaussian.memLp_dual ν K 2 (by norm_num)) hz₂]
  rw [variance_const_mul, variance_fun_id_gaussianReal]
  ring

def rankOneResidual (d : E) (L : E →L[ℝ] ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - L.smulRight d

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem rankOneResidual_apply (d : E) (L : E →L[ℝ] ℝ) (x : E) :
    rankOneResidual d L x = x - L x • d := by simp [rankOneResidual]

/-- Construct the independent residual/range-coordinate split of an existing
Gaussian vector. The covariance duality hypothesis is the algebraic range
condition; no score estimate, density formula, or independence is assumed.
For a finite covariance matrix C and physical direction d, it is obtained
from `C a=d` by normalizing the continuous linear functional `aᵀ`.
-/
theorem gaussian_rankOne_factorization [CompleteSpace E]
    (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ) (d : E)
    (hMean : ∫ x, L x ∂μ = 0) (hVar : 0 < Var[L; μ])
    (hCov : ∀ K : E →L[ℝ] ℝ, cov[K, L; μ] = Var[L; μ] * K d) :
    L d = 1 ∧ ∃ ν : Measure E, IsGaussian ν ∧
      (∀ᵐ x ∂ν, L x = 0) ∧
      μ = rankOneGaussianLaw ν d (Var[L; μ]).toNNReal := by
  have hLd : L d = 1 := by
    have h := hCov L
    rw [covariance_self (by fun_prop)] at h
    apply mul_left_cancel₀ hVar.ne'
    simpa only [mul_one] using h.symm
  let R : E →L[ℝ] E := rankOneResidual d L
  have hRker (x : E) : L (R x) = 0 := by
    simp only [R, rankOneResidual_apply, map_sub, map_smul, hLd, smul_eq_mul, mul_one,
      sub_self]
  have hJoint : HasGaussianLaw (fun x : E => (R x, L x)) μ := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.prod_apply] using
      (IsGaussian.hasGaussianLaw_id (μ := μ)).map_fun (R.prod L)
  have hIndep : IndepFun R L μ := hJoint.indepFun_of_covariance_strongDual (by
    intro K A
    have hA (z : ℝ) : A z = A 1 * z := by
      simpa only [smul_eq_mul, mul_one, mul_comm] using A.map_smul z (1 : ℝ)
    have hAf : (A ∘ L) = fun x : E => A 1 * L x := by
      funext x
      exact hA (L x)
    have hKf : (K ∘ R) = fun x : E => K x - K d * L x := by
      funext x
      simp only [Function.comp_def, R, rankOneResidual_apply, map_sub, map_smul, smul_eq_mul]
      ring
    have hK₂ := IsGaussian.memLp_dual μ K 2 (by norm_num)
    have hL₂ := IsGaussian.memLp_dual μ L 2 (by norm_num)
    have hScalar₂ : MemLp (fun x : E => K d * L x) 2 μ := by
      convert! hL₂.const_mul (K d) using 1
    rw [hAf, covariance_const_mul_right, hKf,
      covariance_fun_sub_left hK₂ hScalar₂ hL₂, covariance_const_mul_left,
      covariance_self (by fun_prop), hCov K]
    ring)
  let ν : Measure E := μ.map R
  have hνGaussian : IsGaussian ν := by dsimp [ν]; infer_instance
  have hνker : ∀ᵐ x ∂ν, L x = 0 := by
    change ∀ᵐ x ∂μ.map R, L x = 0
    rw [ae_map_iff (by fun_prop) ((isClosed_eq L.continuous continuous_const).measurableSet)]
    exact Filter.Eventually.of_forall hRker
  refine ⟨hLd, ν, hνGaussian, hνker, ?_⟩
  have hprod := hIndep.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  have hLlaw : μ.map L = gaussianReal 0 (Var[L; μ]).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal L, hMean]
  calc
    μ = μ.map (fun x : E => x) := by simp
    _ = (μ.map (fun x : E => (R x, L x))).map (rankOneAdd d) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      simp only [Function.comp_def, rankOneAdd_apply, R, rankOneResidual_apply,
        sub_add_cancel]
    _ = (ν.prod (gaussianReal 0 (Var[L; μ]).toNNReal)).map (rankOneAdd d) := by
      rw [hprod, hLlaw]
    _ = rankOneGaussianLaw ν d (Var[L; μ]).toNNReal := rfl

end RankOneGaussianFamilies

section CovarianceRange

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The centered covariance response to a continuous linear observation. This
uses Riesz representation of the actual covariance bilinear form and is well
defined for singular Gaussian laws; no matrix inverse is introduced. -/
def covarianceResponse (μ : Measure E) (L : E →L[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    (covarianceBilin μ ((InnerProductSpace.toDual ℝ E).symm L))

theorem covarianceResponse_duality (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) :
    K (covarianceResponse μ L) = cov[K, L; μ] := by
  let a := (InnerProductSpace.toDual ℝ E).symm L
  let b := (InnerProductSpace.toDual ℝ E).symm K
  calc
    K (covarianceResponse μ L) =
        inner ℝ b (covarianceResponse μ L) := by
      exact (InnerProductSpace.toDual_symm_apply).symm
    _ = inner ℝ (covarianceResponse μ L) b := real_inner_comm _ _
    _ = covarianceBilin μ a b := by
      exact InnerProductSpace.toDual_symm_apply
    _ = covarianceBilin μ b a := covarianceBilin_comm _ _
    _ = cov[K, L; μ] := by
      rw [covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id (μ := μ))]
      congr 1 <;> funext x <;> exact InnerProductSpace.toDual_symm_apply

omit [SecondCountableTopology E] in
theorem covarianceResponse_add_smul (μ : Measure E) (L K : E →L[ℝ] ℝ) (s t : ℝ) :
    covarianceResponse μ (s • L + t • K) =
      s • covarianceResponse μ L + t • covarianceResponse μ K := by
  simp only [covarianceResponse, map_add, map_smul]

/-- A zero-variance Gaussian observation has zero physical covariance
response, including when the full Gaussian law is singular. -/
theorem covarianceResponse_eq_zero_of_variance_eq_zero (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) (hMean : ∫ x, L x ∂μ = 0) (hVar : Var[L; μ] = 0) :
    covarianceResponse μ L = 0 := by
  have hae := ae_eq_integral_of_variance_eq_zero
    (IsGaussian.memLp_dual μ L 2 (by norm_num)) hVar
  rw [hMean] at hae
  let K : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E (covarianceResponse μ L)
  have hc : cov[K, L; μ] = 0 := by
    unfold covariance
    rw [hMean]
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with x hx
    simp [hx]
  have h := (covarianceResponse_duality μ L K).trans hc
  have hi : inner ℝ (covarianceResponse μ L) (covarianceResponse μ L) = 0 := h
  exact inner_self_eq_zero.mp hi

/-- Normalizing a positive-variance covariance response gives the physical
rank-one direction attached to its actual Gaussian range coordinate. -/
def normalizedCovarianceResponse (μ : Measure E) (L : E →L[ℝ] ℝ) : E :=
  (Var[L; μ])⁻¹ • covarianceResponse μ L

theorem normalizedCovarianceResponse_duality (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) (hVar : 0 < Var[L; μ]) (K : E →L[ℝ] ℝ) :
    cov[K, L; μ] = Var[L; μ] * K (normalizedCovarianceResponse μ L) := by
  simp only [normalizedCovarianceResponse, map_smul, smul_eq_mul,
    covarianceResponse_duality]
  field_simp

/-- Every centered positive-variance observation of an actual Gaussian vector
constructs an independent Gaussian residual and exact one-dimensional range
factor. Degenerate complementary covariance is allowed without a condition
number or an assumed independence statement. -/
theorem gaussian_covariance_range_factorization (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) (hMean : ∫ x, L x ∂μ = 0) (hVar : 0 < Var[L; μ]) :
    L (normalizedCovarianceResponse μ L) = 1 ∧
      ∃ ν : Measure E, IsGaussian ν ∧ (∀ᵐ x ∂ν, L x = 0) ∧
        μ = rankOneGaussianLaw ν (normalizedCovarianceResponse μ L)
          (Var[L; μ]).toNNReal := by
  exact gaussian_rankOne_factorization μ L (normalizedCovarianceResponse μ L)
    hMean hVar (normalizedCovarianceResponse_duality μ L hVar)

/-- Every physical component of the extracted scalar fraction has variance
bounded by its full original Gaussian variance. The estimate has no inverse
covariance or condition number. -/
theorem covariance_range_component_variance_bound (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) (hMean : ∫ x, L x ∂μ = 0) (hVar : 0 < Var[L; μ])
    (K : E →L[ℝ] ℝ) :
    Var[L; μ] * (K (normalizedCovarianceResponse μ L)) ^ 2 ≤ Var[K; μ] := by
  obtain ⟨_, ν, hν, _, hμ⟩ :=
    gaussian_covariance_range_factorization μ L hMean hVar
  have : IsGaussian ν := hν
  have h := variance_rankOneGaussianLaw ν (normalizedCovarianceResponse μ L)
    (Var[L; μ]).toNNReal K
  rw [← hμ, Real.coe_toNNReal _ hVar.le] at h
  linarith [variance_nonneg K ν]

/-- The usual covariance Cauchy--Schwarz estimate, obtained here from the
actual independent Gaussian residual rather than an invertible Gram matrix. -/
theorem covarianceResponse_energy_bound (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) (hMean : ∫ x, L x ∂μ = 0) (hVar : 0 < Var[L; μ])
    (K : E →L[ℝ] ℝ) :
    (K (covarianceResponse μ L)) ^ 2 ≤ Var[L; μ] * Var[K; μ] := by
  have h := covariance_range_component_variance_bound μ L hMean hVar K
  dsimp only [normalizedCovarianceResponse] at h
  rw [map_smul, smul_eq_mul] at h
  have h' := mul_le_mul_of_nonneg_left h hVar.le
  field_simp at h'
  nlinarith

/-- Exact finite Gaussian likelihood ratio along an actual covariance range
direction. This is a global integral identity for bounded measurable tests,
including singular complementary covariance. -/
theorem gaussian_covarianceResponse_mean_likelihood (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) (hMean : ∫ x, L x ∂μ = 0) (hVar : 0 < Var[L; μ])
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (s : ℝ) :
    (∫ y, F (y + s • covarianceResponse μ L) ∂μ) =
      ∫ y, F y * Real.exp (s * L y - s ^ 2 * Var[L; μ] / 2) ∂μ := by
  let v : ℝ≥0 := (Var[L; μ]).toNNReal
  have hv : (v : ℝ) = Var[L; μ] := Real.coe_toNNReal _ hVar.le
  have hv0 : v ≠ 0 := by exact_mod_cast (hv.symm ▸ hVar.ne')
  obtain ⟨hLd, ν, hν, hker, hμ⟩ :=
    gaussian_covariance_range_factorization μ L hMean hVar
  have : IsGaussian ν := hν
  let d : E := normalizedCovarianceResponse μ L
  have hd : (s * Var[L; μ]) • d = s • covarianceResponse μ L := by
    dsimp [d, normalizedCovarianceResponse]
    rw [smul_smul]
    congr 1
    field_simp
  have hμ' : rankOneGaussianLaw ν d v = μ := hμ.symm
  have hscore := rankOne_score_integral ν d v F hF M hB L hLd hker
    (meanTilt v (s * Var[L; μ])) (by unfold meanTilt; fun_prop)
    (integrable_meanTilt v (s * Var[L; μ]))
  calc
    _ = rankOneMeanExpectation ν d v F (s * Var[L; μ]) := by
      unfold rankOneMeanExpectation
      rw [hd, hμ']
    _ = gaussianConvolution v (rankOneAverage ν d F) (s * Var[L; μ]) := by
      rw [rankOneMeanExpectation_eq_convolution ν d v F hF M hB]
    _ = ∫ z, rankOneAverage ν d F z * meanTilt v (s * Var[L; μ]) z
        ∂gaussianReal 0 v := by
      rw [← gaussian_mean_integral_eq_convolution v (rankOneAverage ν d F)
        (measurable_rankOneAverage ν d F hF), gaussian_mean_integral_eq_tilt v hv0]
    _ = ∫ y, F y * meanTilt v (s * Var[L; μ]) (L y) ∂μ := by
      rw [← hscore, hμ']
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only [meanTilt]
        rw [hv]
        congr 2
        field_simp
        )

/-- The exact likelihood identity also includes every zero-variance direction.
In those directions the physical covariance response is zero and the scalar
observation is almost surely zero. -/
theorem gaussian_covarianceResponse_mean_likelihood_all (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) (hMean : ∫ x, L x ∂μ = 0)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (s : ℝ) :
    (∫ y, F (y + s • covarianceResponse μ L) ∂μ) =
      ∫ y, F y * Real.exp (s * L y - s ^ 2 * Var[L; μ] / 2) ∂μ := by
  by_cases hv : Var[L; μ] = 0
  · have hr := covarianceResponse_eq_zero_of_variance_eq_zero μ L hMean hv
    have hae := ae_eq_integral_of_variance_eq_zero
      (IsGaussian.memLp_dual μ L 2 (by norm_num)) hv
    rw [hMean] at hae
    rw [hr]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    simp [hx, hv]
  · exact gaussian_covarianceResponse_mean_likelihood μ L hMean
      (lt_of_le_of_ne (variance_nonneg L μ) (Ne.symm hv)) F hF M hB s

/-- The finite Gaussian likelihood ratio is an equality of actual measures,
so it also applies to integrable unbounded test functions. -/
theorem gaussian_covarianceResponse_mean_map_withDensity
    (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ)
    (hMean : ∫ x, L x ∂μ = 0) (s : ℝ) :
    μ.map (fun x => x + s • covarianceResponse μ L) =
      μ.withDensity (fun x => ENNReal.ofReal
        (Real.exp (s * L x - s ^ 2 * Var[L; μ] / 2))) := by
  let g : E → ℝ := fun x => Real.exp (s * L x - s ^ 2 * Var[L; μ] / 2)
  have hLaw : HasLaw L (gaussianReal 0 (Var[L; μ]).toNNReal) μ := {
    aemeasurable := by fun_prop
    map_eq := by rw [IsGaussian.map_eq_gaussianReal L, hMean] }
  have hg : Integrable g μ := by
    have h := hLaw.integrable_comp
      (integrable_exp_mul_gaussianReal (μ := 0) (v := (Var[L; μ]).toNNReal) s)
    convert! h.const_mul (Real.exp (-(s ^ 2 * Var[L; μ] / 2))) using 1
    ext x
    dsimp only [g, Function.comp_def]
    rw [← Real.exp_add]
    congr 1
    ring
  have : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (g x))) :=
    isFiniteMeasure_withDensity_ofReal hg.2
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (μ.map (fun x => x + s • covarianceResponse μ L)).real A =
    (μ.withDensity (fun x => ENNReal.ofReal (g x))).real A
  rw [← integral_indicator_one hA,
    integral_map (by fun_prop) (by fun_prop),
    withDensity_real_apply_eq_integral (by fun_prop) (by simp) hA.nullMeasurableSet]
  simp only [g, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have h := gaussian_covarianceResponse_mean_likelihood_all μ L hMean
    (A.indicator 1) (measurable_const.indicator hA) 1
    (fun x => by by_cases hx : x ∈ A <;> simp [Set.indicator, hx]) s
  rw [← integral_indicator hA]
  convert! h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx])

/-- Actual mean-translation likelihood for every measurable test. Integrable
polynomially weighted tests are included without a boundedness assumption. -/
theorem gaussian_covarianceResponse_mean_likelihood_measurable
    (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ)
    (hMean : ∫ x, L x ∂μ = 0) (F : E → ℝ) (hF : Measurable F) (s : ℝ) :
    (∫ y, F (y + s • covarianceResponse μ L) ∂μ) =
      ∫ y, F y * Real.exp (s * L y - s ^ 2 * Var[L; μ] / 2) ∂μ := by
  rw [← integral_map (by fun_prop) hF.aestronglyMeasurable,
    gaussian_covarianceResponse_mean_map_withDensity μ L hMean s,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
    ring)

/-- Exact fixed-measure likelihood formula for a Gaussian mean comparison
with a retained linear score. The cross covariance correction is explicit. -/
theorem gaussian_weighted_mean_likelihood (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) (hK0 : ∫ x, K x ∂μ = 0)
    (F : E → ℝ) (hF : Measurable F) (s : ℝ) :
    (∫ y, F (y + s • covarianceResponse μ K) * L y ∂μ) =
      ∫ y, F y * (L y - s * cov[L, K; μ]) *
        Real.exp (s * K y - s ^ 2 * Var[K; μ] / 2) ∂μ := by
  have h := gaussian_covarianceResponse_mean_likelihood_measurable μ K hK0
    (fun y => F y * (L y - s * cov[L, K; μ])) (by fun_prop) s
  convert! h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [map_add, map_smul, covarianceResponse_duality]
    simp only [smul_eq_mul]
    ring)

/-- Exact two-parameter physical Gaussian mean comparison, with the full
cross covariance retained. It is valid on singular covariance ranges. -/
theorem gaussian_two_mean_likelihood (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) (hL0 : ∫ x, L x ∂μ = 0) (hK0 : ∫ x, K x ∂μ = 0)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (s t : ℝ) :
    (∫ y, F (y + s • covarianceResponse μ L + t • covarianceResponse μ K) ∂μ) =
      ∫ y, F y * Real.exp (s * L y + t * K y -
        (s ^ 2 * Var[L; μ] + 2 * s * t * cov[L, K; μ] + t ^ 2 * Var[K; μ]) / 2) ∂μ := by
  let A : E →L[ℝ] ℝ := s • L + t • K
  have hA0 : ∫ x, A x ∂μ = 0 := by
    change (∫ x, s * L x + t * K x ∂μ) = 0
    have h := integral_add ((IsGaussian.integrable_dual μ L).const_mul s)
      ((IsGaussian.integrable_dual μ K).const_mul t)
    calc
      _ = (∫ x, s * L x ∂μ) + ∫ x, t * K x ∂μ := by convert! h using 1
      _ = 0 := by simp [integral_const_mul, hL0, hK0]
  have hVar : Var[A; μ] = s ^ 2 * Var[L; μ] +
      2 * s * t * cov[L, K; μ] + t ^ 2 * Var[K; μ] := by
    change Var[fun x => s * L x + t * K x; μ] = _
    rw [variance_fun_add ((IsGaussian.memLp_dual μ L 2 (by norm_num)).const_mul s)
      ((IsGaussian.memLp_dual μ K 2 (by norm_num)).const_mul t), variance_const_mul,
      variance_const_mul, covariance_const_mul_left, covariance_const_mul_right]
    ring
  have h := gaussian_covarianceResponse_mean_likelihood_all μ A hA0 F hF M hB 1
  rw [show A = s • L + t • K from rfl, covarianceResponse_add_smul] at h
  rw [← show Var[A; μ] = Var[s • L + t • K; μ] from rfl, hVar] at h
  convert! h using 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by simp [add_assoc])
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by simp)

/-- A genuine derivative identity for translation along an actual covariance
range direction. The test need only be bounded and measurable; singular
covariance is permitted. The physical score is the observation itself. -/
theorem hasDerivAt_gaussian_covarianceResponse_mean (μ : Measure E) [IsGaussian μ]
    (L : E →L[ℝ] ℝ) (hMean : ∫ x, L x ∂μ = 0) (hVar : 0 < Var[L; μ])
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (m : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ y, F (y + s • covarianceResponse μ L) ∂μ)
      (∫ y, F (y + m • covarianceResponse μ L) * L y ∂μ) m := by
  let v : ℝ≥0 := (Var[L; μ]).toNNReal
  have hv : (v : ℝ) = Var[L; μ] := Real.coe_toNNReal _ hVar.le
  have hv0 : v ≠ 0 := by exact_mod_cast (hv.symm ▸ hVar.ne')
  obtain ⟨hLd, ν, hν, hker, hμ⟩ :=
    gaussian_covariance_range_factorization μ L hMean hVar
  have : IsGaussian ν := hν
  let d : E := normalizedCovarianceResponse μ L
  have hd (s : ℝ) : (s * Var[L; μ]) • d = s • covarianceResponse μ L := by
    dsimp [d, normalizedCovarianceResponse]
    rw [smul_smul]
    congr 1
    field_simp
  have h := hasDerivAt_rankOneMeanExpectation ν d v hv0 F hF M hB L hLd hker
    (m * Var[L; μ])
  have hc := h.comp m ((hasDerivAt_id m).mul_const (Var[L; μ]))
  have heq : (fun s : ℝ => rankOneMeanExpectation ν d v F (s * Var[L; μ])) =
      fun s : ℝ => ∫ y, F (y + s • covarianceResponse μ L) ∂μ := by
    funext s
    unfold rankOneMeanExpectation
    rw [hd s]
    rw [hμ]
  simp only [Function.comp_def, id_eq, one_mul] at hc
  rw [heq] at hc
  have hμ' : rankOneGaussianLaw ν d v = μ := hμ.symm
  rw [hμ'] at hc
  convert! hc using 1
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [hd m]
    dsimp [firstScore]
    rw [hv]
    field_simp)

/-- The second derivative in an actual covariance range direction has the
centered-square score of its actual Gaussian observation. No smoothness of
the bounded test is required. -/
theorem hasDerivAt_deriv_gaussian_covarianceResponse_mean
    (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ)
    (hMean : ∫ x, L x ∂μ = 0) (hVar : 0 < Var[L; μ])
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (m : ℝ) :
    HasDerivAt (deriv (fun s : ℝ => ∫ y, F (y + s • covarianceResponse μ L) ∂μ))
      (∫ y, F (y + m • covarianceResponse μ L) * ((L y) ^ 2 - Var[L; μ]) ∂μ) m := by
  let v : ℝ≥0 := (Var[L; μ]).toNNReal
  have hv : (v : ℝ) = Var[L; μ] := Real.coe_toNNReal _ hVar.le
  have hv0 : v ≠ 0 := by exact_mod_cast (hv.symm ▸ hVar.ne')
  obtain ⟨hLd, ν, hν, hker, hμ⟩ :=
    gaussian_covariance_range_factorization μ L hMean hVar
  have : IsGaussian ν := hν
  let d : E := normalizedCovarianceResponse μ L
  have hd (s : ℝ) : (s * Var[L; μ]) • d = s • covarianceResponse μ L := by
    dsimp [d, normalizedCovarianceResponse]
    rw [smul_smul]
    congr 1
    field_simp
  have hμ' : rankOneGaussianLaw ν d v = μ := hμ.symm
  have heq : (fun s : ℝ => rankOneMeanExpectation ν d v F (s * Var[L; μ])) =
      fun s : ℝ => ∫ y, F (y + s • covarianceResponse μ L) ∂μ := by
    funext s
    unfold rankOneMeanExpectation
    rw [hd s, hμ']
  have hfirst (s : ℝ) :=
    hasDerivAt_rankOneMeanExpectation ν d v hv0 F hF M hB L hLd hker s
  have hderiv : deriv (fun s : ℝ => ∫ y, F (y + s • covarianceResponse μ L) ∂μ) =
      fun s : ℝ => deriv (rankOneMeanExpectation ν d v F) (s * Var[L; μ]) * Var[L; μ] := by
    funext s
    rw [← heq]
    have h := (hfirst (s * Var[L; μ])).comp s
      ((hasDerivAt_id s).mul_const (Var[L; μ]))
    simp only [Function.comp_def, id_eq, one_mul] at h
    rw [h.deriv, (hfirst (s * Var[L; μ])).deriv]
  have hsecond := hasDerivAt_deriv_rankOneMeanExpectation ν d v hv0 F hF M hB L
    hLd hker (m * Var[L; μ])
  have hc := (hsecond.comp m ((hasDerivAt_id m).mul_const (Var[L; μ]))).mul_const
    (Var[L; μ])
  simp only [Function.comp_def, id_eq, one_mul] at hc
  rw [hμ'] at hc
  rw [hderiv]
  convert! hc using 1
  rw [← integral_mul_const, ← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [hd m]
    dsimp [secondScore]
    rw [hv]
    field_simp)

/-- The actual Gaussian covariance perturbation in the physical direction
`covarianceResponse μ L`, built from the independent residual supplied by the
original law. Its derivative is the centered-square score, also for singular
covariance. The quadratic-form identity identifies the physical perturbation. -/
theorem gaussian_covarianceResponse_covariance_derivative
    (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ)
    (hMean : ∫ x, L x ∂μ = 0) (hVar : 0 < Var[L; μ])
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    ∃ ν : Measure E, IsGaussian ν ∧
      (let v := Var[L; μ]
       let d := normalizedCovarianceResponse μ L
       μ = rankOneGaussianLaw ν d v.toNNReal ∧
       (∀ (K : E →L[ℝ] ℝ) (s : ℝ), 0 ≤ v + s * v ^ 2 →
         Var[K; rankOneGaussianLaw ν d (v + s * v ^ 2).toNNReal] =
           Var[K; μ] + s * (K (covarianceResponse μ L)) ^ 2) ∧
       HasDerivAt (fun s : ℝ => ∫ y, F y
         ∂rankOneGaussianLaw ν d (v + s * v ^ 2).toNNReal)
         ((1 / 2 : ℝ) * ∫ y, F y * ((L y) ^ 2 - v) ∂μ) 0) := by
  let v : ℝ≥0 := (Var[L; μ]).toNNReal
  have hv : (v : ℝ) = Var[L; μ] := Real.coe_toNNReal _ hVar.le
  have hv0 : v ≠ 0 := by exact_mod_cast (hv.symm ▸ hVar.ne')
  obtain ⟨hLd, ν, hν, hker, hμ⟩ :=
    gaussian_covariance_range_factorization μ L hMean hVar
  have : IsGaussian ν := hν
  let d : E := normalizedCovarianceResponse μ L
  have hμ' : rankOneGaussianLaw ν d v = μ := hμ.symm
  refine ⟨ν, hν, hμ, ?_, ?_⟩
  · intro K s hs
    have hb := variance_rankOneGaussianLaw ν d v K
    have hp := variance_rankOneGaussianLaw ν d (Var[L; μ] + s * Var[L; μ] ^ 2).toNNReal K
    rw [hμ', hv] at hb
    rw [Real.coe_toNNReal _ hs] at hp
    rw [hp, hb]
    dsimp [d, normalizedCovarianceResponse]
    rw [map_smul, smul_eq_mul]
    field_simp
    ring
  · have h := hasDerivAt_rankOne_variance ν d v hv0 F hF M hB L hLd hker
    have hg := (hasDerivAt_const 0 (v : ℝ)).add
      ((hasDerivAt_id 0).mul_const ((v : ℝ) ^ 2))
    have hpre : HasDerivAt (fun w : ℝ => ∫ y, F y ∂rankOneGaussianLaw ν d w.toNNReal)
        ((1 / 2 : ℝ) * ∫ y, F y * secondScore v (L y) ∂rankOneGaussianLaw ν d v)
        ((v : ℝ) + 0 * (v : ℝ) ^ 2) := by simpa using h
    have hc := hpre.comp 0 hg
    simp only [Function.comp_def, id_eq, zero_add, one_mul] at hc
    rw [hμ', hv] at hc
    convert! hc using 1
    rw [mul_assoc, ← integral_mul_const]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by
      dsimp only [secondScore]
      rw [hv]
      field_simp)

end CovarianceRange

section FiniteFractionCentering

/-- Suppress just one reserved Gaussian fraction, leaving every other
coordinate and every original physical observation in the test unchanged. -/
def fractionDifference {n : ℕ} (i : Fin n) (F : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ := F x - F (Function.update x i 0)

def fractionDifferences {n : ℕ} (is : List (Fin n)) (F : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ := is.foldr fractionDifference F

theorem measurable_fractionDifference {n : ℕ} (i : Fin n)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    Measurable (fractionDifference i F) := by
  unfold fractionDifference
  exact hF.sub (hF.comp (by fun_prop))

theorem fractionDifference_bound {n : ℕ} (i : Fin n)
    (F : (Fin n → ℝ) → ℝ) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (x : Fin n → ℝ) :
    |fractionDifference i F x| ≤ 2 * M := by
  exact (abs_sub _ _).trans (by linarith [hB x, hB (Function.update x i 0)])

/-- A centered coordinate score annihilates every test in which that
coordinate has been suppressed. This is the actual finite-product integral,
proved by a measure-preserving coordinate split and Fubini. -/
theorem integral_product_score_suppressed {n : ℕ}
    (μ : Fin (n + 1) → Measure ℝ) [∀ j, SigmaFinite (μ j)]
    (S : Fin (n + 1) → ℝ → ℝ) (i : Fin (n + 1))
    (hSi : ∫ z, S i z ∂μ i = 0) (F : (Fin (n + 1) → ℝ) → ℝ) :
    (∫ x, (∏ j, S j (x j)) * F (Function.update x i 0) ∂Measure.pi μ) = 0 := by
  rw [← ((measurePreserving_piFinSuccAbove μ i).symm).integral_comp']
  have heq : (fun p : ℝ × (Fin n → ℝ) =>
      (∏ j, S j (((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm p) j)) *
        F (Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm p) i 0)) =
      fun p => S i p.1 * ((∏ j : Fin n, S (i.succAbove j) (p.2 j)) *
        F (Fin.insertNth i 0 p.2)) := by
    funext ⟨z, x⟩
    change (∏ j, S j ((Fin.insertNth i z x : Fin (n + 1) → ℝ) j)) *
      F (Function.update (Fin.insertNth i z x) i 0) = _
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
      Fin.update_insertNth]
    ring
  rw [heq]
  calc
    _ = (∫ z, S i z ∂μ i) *
        ∫ x, (∏ j : Fin n, S (i.succAbove j) (x j)) * F (Fin.insertNth i 0 x)
          ∂Measure.pi (fun j => μ (i.succAbove j)) := integral_prod_mul _ _
    _ = 0 := by rw [hSi, zero_mul]

theorem integrable_product_score_bounded {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ j, SigmaFinite (μ j)]
    (S : Fin n → ℝ → ℝ) (hS : ∀ j, Integrable (S j) (μ j))
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    Integrable (fun x => (∏ j, S j (x j)) * F x) (Measure.pi μ) := by
  exact (Integrable.fintype_prod hS).mul_bdd hF.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))

/-- Exact preservation of a finite Gaussian-score word by one old-fraction
centering, with integrability proved from the actual score moments. -/
theorem integral_product_score_fractionDifference {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ j, SigmaFinite (μ j)]
    (S : Fin n → ℝ → ℝ) (hS : ∀ j, Integrable (S j) (μ j))
    (i : Fin n) (hSi : ∫ z, S i z ∂μ i = 0)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    (∫ x, (∏ j, S j (x j)) * fractionDifference i F x ∂Measure.pi μ) =
      ∫ x, (∏ j, S j (x j)) * F x ∂Measure.pi μ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have h₁ := integrable_product_score_bounded μ S hS F hF M hB
    have h₂ := integrable_product_score_bounded μ S hS
      (fun x => F (Function.update x i 0)) (hF.comp (by fun_prop)) M (fun x => hB _)
    simp only [fractionDifference, mul_sub]
    rw [integral_sub h₁ h₂, integral_product_score_suppressed μ S i hSi, sub_zero]

theorem measurable_fractionDifferences {n : ℕ} (is : List (Fin n))
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    Measurable (fractionDifferences is F) := by
  induction is with
  | nil => exact hF
  | cons i is ih => exact measurable_fractionDifference i _ ih

theorem fractionDifferences_bound {n : ℕ} (is : List (Fin n))
    (F : (Fin n → ℝ) → ℝ) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (x : Fin n → ℝ) :
    |fractionDifferences is F x| ≤ 2 ^ is.length * M := by
  induction is generalizing x with
  | nil => simpa [fractionDifferences] using hB x
  | cons i is ih =>
    have h := fractionDifference_bound i (fractionDifferences is F)
      (2 ^ is.length * M) (fun x => ih x) x
    simpa [fractionDifferences, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

/-- Every finite family of independent centered scores admits the full
iterated old-fraction centering. This is an identity for the actual product
measure and a bounded measurable test, not a formal assumed cancellation. -/
theorem integral_product_score_fractionDifferences {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ j, SigmaFinite (μ j)]
    (S : Fin n → ℝ → ℝ) (hS : ∀ j, Integrable (S j) (μ j))
    (hS0 : ∀ j, ∫ z, S j z ∂μ j = 0) (is : List (Fin n))
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    (∫ x, (∏ j, S j (x j)) * fractionDifferences is F x ∂Measure.pi μ) =
      ∫ x, (∏ j, S j (x j)) * F x ∂Measure.pi μ := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change (∫ x, (∏ j, S j (x j)) * fractionDifference i (fractionDifferences is F) x
      ∂Measure.pi μ) = _
    rw [integral_product_score_fractionDifference μ S hS i (hS0 i)
      (fractionDifferences is F) (measurable_fractionDifferences is F hF)
      (2 ^ is.length * M) (fractionDifferences_bound is F M hB), ih]

/-- Actual independent Gaussian covariance scores admit centering at every
finite order. Each selected coordinate is replaced by zero only in its own
reserved fraction; the test may retain all original observation coordinates. -/
theorem gaussian_secondScores_center_all {n : ℕ} (v : Fin n → ℝ≥0)
    (is : List (Fin n)) (F : (Fin n → ℝ) → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    (∫ x, (∏ j, secondScore (v j) (x j)) * fractionDifferences is F x
      ∂Measure.pi (fun j => gaussianReal 0 (v j))) =
      ∫ x, (∏ j, secondScore (v j) (x j)) * F x
        ∂Measure.pi (fun j => gaussianReal 0 (v j)) := by
  exact integral_product_score_fractionDifferences _ _ (fun j => integrable_secondScore _)
    (fun j => integral_secondScore _) is F hF M hB

/-- A single old fraction is assigned to exactly one root/rough factor.
Earlier factors are evaluated with that fraction suppressed; later factors
retain it. Iteration gives the finite product-difference assignment grammar. -/
theorem fractionDifference_product {n m : ℕ} (i : Fin n)
    (F : Fin m → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    fractionDifference i (fun y => ∏ j, F j y) x =
      ∑ j : Fin m, fractionDifference i (F j) x *
        (∏ k ∈ Finset.univ with k < j, F k (Function.update x i 0)) *
        ∏ k ∈ Finset.univ with j < k, F k x := by
  have h := Finset.prod_sub_ordered (Finset.univ : Finset (Fin m))
    (fun j => F j x) (fun j => F j x - F j (Function.update x i 0))
  simp only [sub_sub_cancel] at h
  dsimp [fractionDifference]
  linarith

theorem fractionDifference_mul {n : ℕ} (i : Fin n)
    (F G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    fractionDifference i (fun y => F y * G y) x =
      fractionDifference i F x * G x +
        F (Function.update x i 0) * fractionDifference i G x := by
  dsimp [fractionDifference]
  ring

/-- If a newest rough leaf is untouched by all old fractions, it survives
every old centering exactly as a factor. -/
theorem fractionDifferences_mul_const {n : ℕ} (is : List (Fin n))
    (F : (Fin n → ℝ) → ℝ) (c : ℝ) :
    fractionDifferences is (fun x => F x * c) =
      fun x => fractionDifferences is F x * c := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change fractionDifference i (fractionDifferences is (fun x => F x * c)) = _
    rw [ih]
    funext x
    dsimp [fractionDifferences, fractionDifference]
    ring

/-- One term of the ordered assignment of one fraction to one factor. The
three exclusive cases are an earlier suppressed factor, the chosen difference,
and a later unchanged factor. -/
def assignFractionFactor {n m : ℕ} (i : Fin n)
    (F : Fin m → (Fin n → ℝ) → ℝ) (j k : Fin m) (x : Fin n → ℝ) : ℝ :=
  (if k < j then F k (Function.update x i 0) else 1) *
    (if k = j then fractionDifference i (F k) x else 1) *
    (if j < k then F k x else 1)

theorem product_assignFractionFactor {n m : ℕ} (i : Fin n)
    (F : Fin m → (Fin n → ℝ) → ℝ) (j : Fin m) (x : Fin n → ℝ) :
    (∏ k, assignFractionFactor i F j k x) =
      fractionDifference i (F j) x *
        (∏ k ∈ Finset.univ with k < j, F k (Function.update x i 0)) *
        ∏ k ∈ Finset.univ with j < k, F k x := by
  simp only [assignFractionFactor, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  rw [← Finset.prod_filter, ← Finset.prod_filter]
  ring

/-- The explicit finite list of factor assignments. At each old fraction
there is exactly one choice of root/rough factor. Its list length is m^n
(including duplicate terms when a difference happens to vanish). -/
def fractionAssignmentFamilies {n m : ℕ} (is : List (Fin n))
    (F : Fin m → (Fin n → ℝ) → ℝ) : List (Fin m → (Fin n → ℝ) → ℝ) :=
  match is with
  | [] => [F]
  | i :: is => (fractionAssignmentFamilies is F).flatMap
      (fun G => List.ofFn (fun j => assignFractionFactor i G j))

def sumProductFamilies {n m : ℕ} (l : List (Fin m → (Fin n → ℝ) → ℝ))
    (x : Fin n → ℝ) : ℝ := (l.map (fun F => ∏ j, F j x)).sum

theorem fractionDifference_sumProductFamilies {n m : ℕ} (i : Fin n)
    (l : List (Fin m → (Fin n → ℝ) → ℝ)) (x : Fin n → ℝ) :
    fractionDifference i (sumProductFamilies l) x =
      (l.map (fun F => fractionDifference i (fun y => ∏ j, F j y) x)).sum := by
  induction l with
  | nil => simp [fractionDifference, sumProductFamilies]
  | cons F l ih =>
    simp only [sumProductFamilies, List.map_cons, List.sum_cons, fractionDifference] at ih ⊢
    linarith

theorem sumProductFamilies_flatMap {n m : ℕ}
    (l : List (Fin m → (Fin n → ℝ) → ℝ))
    (f : (Fin m → (Fin n → ℝ) → ℝ) → List (Fin m → (Fin n → ℝ) → ℝ))
    (x : Fin n → ℝ) :
    sumProductFamilies (l.flatMap f) x =
      (l.map (fun F => sumProductFamilies (f F) x)).sum := by
  induction l with
  | nil => simp [sumProductFamilies]
  | cons F l ih =>
    simpa only [sumProductFamilies, List.flatMap_cons, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons] using congrArg
        (fun a => sumProductFamilies (f F) x + a) ih

/-- An explicit all-order product assignment expansion, obtained by iterating
the exact one-fraction Leibniz rule. No smoothness or stochastic estimate is
used; the same original observation tuple remains in every test factor. -/
theorem fractionDifferences_assignment_expansion {n m : ℕ}
    (is : List (Fin n)) (F : Fin m → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    fractionDifferences is (fun y => ∏ j, F j y) x =
      sumProductFamilies (fractionAssignmentFamilies is F) x := by
  induction is generalizing x with
  | nil => simp [fractionDifferences, fractionAssignmentFamilies, sumProductFamilies]
  | cons i is ih =>
    have heq : fractionDifferences is (fun y => ∏ j, F j y) =
        sumProductFamilies (fractionAssignmentFamilies is F) := funext ih
    change fractionDifference i (fractionDifferences is (fun y => ∏ j, F j y)) x = _
    rw [heq, fractionDifference_sumProductFamilies]
    rw [fractionAssignmentFamilies, sumProductFamilies_flatMap]
    congr 1
    apply List.map_congr_left
    intro G hG
    rw [fractionDifference_product]
    simp only [sumProductFamilies, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    apply Finset.sum_congr rfl
    intro j hj
    exact (product_assignFractionFactor i G j x).symm

/-- The complete algebraic finite-order Gaussian word: the actual product
score integral equals the integral of its explicitly generated assignments. -/
theorem gaussian_word_assignment_identity {n m : ℕ} (v : Fin n → ℝ≥0)
    (is : List (Fin n)) (F : Fin m → (Fin n → ℝ) → ℝ)
    (hF : ∀ j, Measurable (F j)) (M : ℝ) (hB : ∀ x, |∏ j, F j x| ≤ M) :
    (∫ x, (∏ j, secondScore (v j) (x j)) * (∏ j, F j x)
      ∂Measure.pi (fun j => gaussianReal 0 (v j))) =
      ∫ x, (∏ j, secondScore (v j) (x j)) *
        sumProductFamilies (fractionAssignmentFamilies is F) x
          ∂Measure.pi (fun j => gaussianReal 0 (v j)) := by
  rw [← gaussian_secondScores_center_all v is (fun y => ∏ j, F j y)
    (by fun_prop) M hB]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [fractionDifferences_assignment_expansion]))

theorem fractionDifference_comm {n : ℕ} (i j : Fin n)
    (F : (Fin n → ℝ) → ℝ) :
    fractionDifference i (fractionDifference j F) =
      fractionDifference j (fractionDifference i F) := by
  funext x
  dsimp [fractionDifference]
  by_cases h : i = j
  · subst j
    rfl
  · rw [Function.update_comm h]
    ring

theorem fractionDifference_comm_differences {n : ℕ} (i : Fin n)
    (is : List (Fin n)) (F : (Fin n → ℝ) → ℝ) :
    fractionDifference i (fractionDifferences is F) =
      fractionDifferences is (fractionDifference i F) := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    change fractionDifference i (fractionDifference j (fractionDifferences is F)) = _
    rw [fractionDifference_comm, ih]
    rfl

/-- Centering coordinates other than i preserves any envelope depending only
on the size of the i-th fraction. This is what allows a mixed block to use
its smallest old increment without multiplying all increment sizes. -/
theorem fractionDifferences_coordinate_bound {n : ℕ} (i : Fin n)
    (is : List (Fin n)) (hi : i ∉ is) (F : (Fin n → ℝ) → ℝ)
    (B : ℝ → ℝ) (hB : ∀ x, |F x| ≤ B (x i)) (x : Fin n → ℝ) :
    |fractionDifferences is F x| ≤ 2 ^ is.length * B (x i) := by
  induction is generalizing x with
  | nil => simpa [fractionDifferences] using hB x
  | cons j is ih =>
    have hij : i ≠ j := by intro h; exact hi (by simp [h])
    have hit : i ∉ is := fun h => hi (by simp [h])
    have h₁ := ih hit x
    have h₂ := ih hit (Function.update x j 0)
    rw [Function.update_of_ne hij] at h₂
    change |fractionDifferences is F x -
      fractionDifferences is F (Function.update x j 0)| ≤ _
    have h := abs_sub (fractionDifferences is F x)
      (fractionDifferences is F (Function.update x j 0))
    simp only [List.length_cons, pow_succ]
    nlinarith

/-- The deterministic mixed-block minimum rule. For every selected fraction
i the block is bounded by its own single-fraction envelope, with only a
finite-order factor 2^(r-1). Choosing the smallest envelope gives the min-gap
bound used for root and rough-leaf blocks. -/
theorem fractionDifferences_block_bound {n : ℕ} (is : List (Fin n)) (hnd : is.Nodup)
    (F : (Fin n → ℝ) → ℝ) (i : Fin n) (hi : i ∈ is) (B : ℝ → ℝ)
    (hB : ∀ x, |fractionDifference i F x| ≤ B (x i)) (x : Fin n → ℝ) :
    |fractionDifferences is F x| ≤ 2 ^ (is.length - 1) * B (x i) := by
  induction is generalizing x with
  | nil => simp at hi
  | cons j is ih =>
    obtain ⟨hj, hnd⟩ := List.nodup_cons.mp hnd
    by_cases hij : i = j
    · subst j
      change |fractionDifference i (fractionDifferences is F) x| ≤ _
      rw [fractionDifference_comm_differences]
      simpa using fractionDifferences_coordinate_bound i is hj
        (fractionDifference i F) B hB x
    · have hit : i ∈ is := (List.mem_cons.mp hi).resolve_left hij
      have h₁ := ih hnd hit x
      have h₂ := ih hnd hit (Function.update x j 0)
      rw [Function.update_of_ne hij] at h₂
      have hlen : 1 ≤ is.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hit)
      have hp : (2 : ℝ) ^ is.length = 2 ^ (is.length - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hlen]
      change |fractionDifferences is F x -
        fractionDifferences is F (Function.update x j 0)| ≤ _
      have h := abs_sub (fractionDifferences is F x)
        (fractionDifferences is F (Function.update x j 0))
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [hp]
      nlinarith

end FiniteFractionCentering

section GaussianFractionalMoments

def gaussianAbsMoment (p : ℝ) : ℝ :=
  ∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1

theorem integrable_gaussian_abs_rpow (v : ℝ≥0) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun z : ℝ => |z| ^ p) (gaussianReal 0 v) := by
  have h := (IsGaussian.memLp_id (gaussianReal 0 v) (ENNReal.ofReal p)
    (by simp)).integrable_norm_rpow'
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp, id_eq] using h

/-- The actual fractional Gaussian moments needed for rough coefficient
increments, including zero variance. -/
theorem gaussian_abs_rpow_moment (v : ℝ≥0) (p : ℝ) (hp : 0 ≤ p) :
    (∫ z : ℝ, |z| ^ p ∂gaussianReal 0 v) =
      (v : ℝ) ^ (p / 2) * gaussianAbsMoment p := by
  rw [← gaussian_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (v : ℝ)),
    Real.mul_rpow (Real.sqrt_nonneg (v : ℝ)) (abs_nonneg _)]
  rw [integral_const_mul, ← Real.rpow_div_two_eq_sqrt p v.coe_nonneg]
  rfl

theorem gaussianAbsMoment_nonneg (p : ℝ) : 0 ≤ gaussianAbsMoment p :=
  integral_nonneg (fun z => Real.rpow_nonneg (abs_nonneg z) p)

/-- A physical component of a reserved scalar Gaussian fraction has all
fractional moments controlled by its full physical variance envelope. -/
theorem gaussian_reserved_component_moment_le (v : ℝ≥0) (c V p : ℝ)
    (hp : 0 ≤ p) (hV : (v : ℝ) * c ^ 2 ≤ V) :
    (∫ z : ℝ, |c * z| ^ p ∂gaussianReal 0 v) ≤
      V ^ (p / 2) * gaussianAbsMoment p := by
  let w : ℝ≥0 := ⟨c ^ 2, sq_nonneg c⟩ * v
  have hw : (w : ℝ) = (v : ℝ) * c ^ 2 := by
    change c ^ 2 * (v : ℝ) = (v : ℝ) * c ^ 2
    exact mul_comm _ _
  calc
    _ = ∫ z : ℝ, |z| ^ p ∂(gaussianReal 0 v).map (fun z : ℝ => c * z) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = (w : ℝ) ^ (p / 2) * gaussianAbsMoment p := by
      rw [gaussianReal_map_const_mul, mul_zero]
      exact gaussian_abs_rpow_moment w p hp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow w.coe_nonneg (hw.symm ▸ hV) (by positivity))
      (gaussianAbsMoment_nonneg p)

theorem memLp_gaussian_abs_rpow_two (v : ℝ≥0) (p : ℝ) (hp : 0 ≤ p) :
    MemLp (fun z : ℝ => |z| ^ p) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := integrable_gaussian_abs_rpow v (p * 2) (by positivity)
  simpa only [Real.rpow_mul (abs_nonneg _), Real.rpow_two] using h

theorem integrable_secondScore_abs_rpow (v : ℝ≥0) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun z : ℝ => |secondScore v z| * |z| ^ p) (gaussianReal 0 v) := by
  have h₂ : MemLp (secondScore v) 2 (gaussianReal 0 v) :=
    (memLp_two_iff_integrable_sq (by unfold secondScore; fun_prop)).mpr
      (integrable_secondScore_power v 2)
  convert! h₂.norm.integrable_mul (memLp_gaussian_abs_rpow_two v p hp) using 1

def secondScoreAbsIncrementMoment (p : ℝ) : ℝ :=
  ∫ z : ℝ, |secondScore 1 z| * |z| ^ p ∂gaussianReal 0 1

/-- Exact scaling of a covariance score multiplied by a rough increment.
This supplies v^(β/2) in an assigned rough block in addition to its score v⁻¹. -/
theorem secondScore_abs_increment_moment (v : ℝ≥0) (hv : v ≠ 0) (p : ℝ) (hp : 0 ≤ p) :
    (∫ z : ℝ, |secondScore v z| * |z| ^ p ∂gaussianReal 0 v) =
      ((v : ℝ) ^ (p / 2) / (v : ℝ)) * secondScoreAbsIncrementMoment p := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [← gaussian_map_sqrt v, integral_map (by fun_prop)
    (by unfold secondScore; fun_prop)]
  have hscore (z : ℝ) : |secondScore v (Real.sqrt (v : ℝ) * z)| =
      |secondScore 1 z| / (v : ℝ) := by
    rw [secondScore_scaled hv z, abs_div, abs_of_nonneg v.coe_nonneg]
    simp [secondScore]
  simp_rw [hscore, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (v : ℝ)),
    Real.mul_rpow (Real.sqrt_nonneg (v : ℝ)) (abs_nonneg _)]
  have heq (z : ℝ) : (|secondScore 1 z| / (v : ℝ)) *
      ((Real.sqrt (v : ℝ)) ^ p * |z| ^ p) =
      ((v : ℝ) ^ (p / 2) / (v : ℝ)) * (|secondScore 1 z| * |z| ^ p) := by
    rw [← Real.rpow_div_two_eq_sqrt p v.coe_nonneg]
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  rfl

/-- A full finite Gaussian old-score block has the precise fractional
variance gain of any one of its assigned increments. This is an actual
integral estimate, derived from deterministic mixed centering and Gaussian
fraction moments; taking the best selected i gives the minimum-gap rule. -/
theorem gaussian_score_block_variance_bound {n : ℕ} (v : Fin n → ℝ≥0)
    (hv : ∀ j, v j ≠ 0) (is : List (Fin n)) (hnd : is.Nodup)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) (i : Fin n) (hi : i ∈ is)
    (p : ℝ) (hp : 0 ≤ p) (C : ℝ)
    (hB : ∀ x, |fractionDifference i F x| ≤ C * |x i| ^ p) :
    Integrable (fun x => |(∏ j, secondScore (v j) (x j)) *
      fractionDifferences is F x|) (Measure.pi (fun j => gaussianReal 0 (v j))) ∧
    (∫ x, |(∏ j, secondScore (v j) (x j)) * fractionDifferences is F x|
      ∂Measure.pi (fun j => gaussianReal 0 (v j))) ≤
      (2 ^ (is.length - 1) * C) *
        ∏ j, (((v j : ℝ) ^ ((if j = i then p else 0) / 2) / (v j : ℝ)) *
          secondScoreAbsIncrementMoment (if j = i then p else 0)) := by
  let μ : Fin n → Measure ℝ := fun j => gaussianReal 0 (v j)
  let Q : Fin n → ℝ → ℝ := fun j z => |secondScore (v j) z| *
    (if j = i then |z| ^ p else 1)
  have hQ : ∀ j, Integrable (Q j) (μ j) := by
    intro j
    by_cases hji : j = i
    · simpa only [Q, hji, ite_true] using integrable_secondScore_abs_rpow (v i) p hp
    · simpa only [Q, hji, ite_false, mul_one, Real.norm_eq_abs] using
        (integrable_secondScore (v j)).norm
  have hQI : Integrable (fun x => (2 ^ (is.length - 1) * C) * ∏ j, Q j (x j))
      (Measure.pi μ) := (Integrable.fintype_prod hQ).const_mul _
  have hprod (x : Fin n → ℝ) : (∏ j, Q j (x j)) =
      (∏ j, |secondScore (v j) (x j)|) * |x i| ^ p := by
    simp only [Q, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  have hbound (x : Fin n → ℝ) :
      |(∏ j, secondScore (v j) (x j)) * fractionDifferences is F x| ≤
        (2 ^ (is.length - 1) * C) * ∏ j, Q j (x j) := by
    have hb := fractionDifferences_block_bound is hnd F i hi
      (fun z => C * |z| ^ p) hB x
    rw [abs_mul, Finset.abs_prod, hprod]
    have hnonneg : 0 ≤ ∏ j, |secondScore (v j) (x j)| :=
      Finset.prod_nonneg (fun _ _ => abs_nonneg _)
    nlinarith
  have hleft : Integrable (fun x => |(∏ j, secondScore (v j) (x j)) *
      fractionDifferences is F x|) (Measure.pi μ) := by
    refine hQI.mono' ?_ (Filter.Eventually.of_forall (fun x => ?_))
    · convert! ((by unfold secondScore; fun_prop : Measurable
        (fun x : Fin n → ℝ => ∏ j, secondScore (v j) (x j))).mul
          (measurable_fractionDifferences is F hF)).norm.aestronglyMeasurable using 1
    · simpa only [Real.norm_eq_abs, abs_abs] using hbound x
  refine ⟨hleft, ?_⟩
  calc
    _ ≤ ∫ x, (2 ^ (is.length - 1) * C) * ∏ j, Q j (x j) ∂Measure.pi μ :=
      integral_mono hleft hQI hbound
    _ = (2 ^ (is.length - 1) * C) * ∏ j, ∫ z, Q j z ∂μ j := by
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have heq : Q j = fun z => |secondScore (v j) z| *
          |z| ^ (if j = i then p else 0) := by
        funext z
        by_cases hji : j = i <;> simp [Q, hji]
      rw [heq]
      exact secondScore_abs_increment_moment (v j) (hv j)
        (if j = i then p else 0) (by split_ifs <;> positivity)

end GaussianFractionalMoments

section MixedGaussianScores

theorem centered_product_even_power_bound (a b c : ℝ) (m : ℕ) :
    |a * b - c| ^ (2 * m) ≤
      2 ^ (2 * m - 1) * ((a ^ (4 * m) + b ^ (4 * m)) / 2 + c ^ (2 * m)) := by
  have hy : (a * b) ^ (2 * m) ≤ (a ^ (4 * m) + b ^ (4 * m)) / 2 := by
    have h := sq_nonneg (a ^ (2 * m) - b ^ (2 * m))
    have ha : (a ^ (2 * m)) ^ 2 = a ^ (4 * m) := by rw [← pow_mul]; congr 1; omega
    have hb : (b ^ (2 * m)) ^ 2 = b ^ (4 * m) := by rw [← pow_mul]; congr 1; omega
    rw [sub_sq, ha, hb] at h
    rw [mul_pow]
    nlinarith
  have hadd := (even_two_mul m).add_pow_le (a := a * b) (b := -c)
  have hneg : (-c) ^ (2 * m) = c ^ (2 * m) := (even_two_mul m).neg_pow c
  rw [hneg, ← sub_eq_add_neg] at hadd
  simp only [pow_abs_two_mul]
  exact hadd.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The actual mixed covariance Hermite score is centered even when the
two Gaussian observations are correlated. -/
theorem integral_gaussian_mixed_score (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) (hL0 : ∫ x, L x ∂μ = 0) (hK0 : ∫ x, K x ∂μ = 0) :
    (∫ x, L x * K x - cov[L, K; μ] ∂μ) = 0 := by
  have hL₂ := IsGaussian.memLp_dual μ L 2 (by norm_num)
  have hK₂ := IsGaussian.memLp_dual μ K 2 (by norm_num)
  have hc := covariance_eq_sub hL₂ hK₂
  rw [hL0, hK0, zero_mul, sub_zero] at hc
  change cov[L, K; μ] = ∫ x, L x * K x ∂μ at hc
  calc
    _ = (∫ x, L x * K x ∂μ) - ∫ _ : E, cov[L, K; μ] ∂μ := by
      convert! integral_sub (hL₂.integrable_mul hK₂) (integrable_const _) using 1
    _ = 0 := by simp [hc]

/-- Algebraic polarization identifies the mixed covariance score with
rank-one centered-square scores of actual Gaussian observations. -/
theorem gaussian_mixed_score_polarization (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) (x : E) :
    L x * K x - cov[L, K; μ] =
      (1 / 2 : ℝ) * (((L x + K x) ^ 2 - Var[fun y => L y + K y; μ]) -
        ((L x) ^ 2 - Var[L; μ]) - ((K x) ^ 2 - Var[K; μ])) := by
  rw [variance_fun_add (IsGaussian.memLp_dual μ L 2 (by norm_num))
    (IsGaussian.memLp_dual μ K 2 (by norm_num))]
  ring

/-- Actual higher moments of the normalized mixed covariance Hermite score.
The observations may be correlated or part of a singular Gaussian vector.
Only their actual variance normalizations are required. -/
theorem gaussian_normalized_mixed_score_even_moment (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) (hL0 : ∫ x, L x ∂μ = 0) (hK0 : ∫ x, K x ∂μ = 0)
    (hL1 : Var[L; μ] ≤ 1) (hK1 : Var[K; μ] ≤ 1) (m : ℕ) :
    Integrable (fun x => |L x * K x - cov[L, K; μ]| ^ (2 * m)) μ ∧
    (∫ x, |L x * K x - cov[L, K; μ]| ^ (2 * m) ∂μ) ≤
      2 ^ (2 * m - 1) * (firstScoreMoment (2 * m) + 1) := by
  have hL₂ := IsGaussian.memLp_dual μ L 2 (by norm_num)
  have hK₂ := IsGaussian.memLp_dual μ K 2 (by norm_num)
  have hc : |cov[L, K; μ]| ≤ 1 := by
    have hp := variance_fun_add hL₂ hK₂
    have hn := variance_fun_sub hL₂ hK₂
    have hpn := variance_nonneg (fun x => L x + K x) μ
    have hnn := variance_nonneg (fun x => L x - K x) μ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hL := gaussian_projection_even_moment μ L (2 * m)
  have hK := gaussian_projection_even_moment μ K (2 * m)
  simp only [hL0, hK0, sub_zero, pow_abs_two_mul] at hL hK
  have hexp : 2 * (2 * m) = 4 * m := by omega
  rw [hexp] at hL hK
  let c : ℝ := cov[L, K; μ]
  let A : ℝ := 2 ^ (2 * m - 1)
  let R : E → ℝ := fun x => A * (((L x) ^ (4 * m) + (K x) ^ (4 * m)) / 2 +
    c ^ (2 * m))
  have hR : Integrable R μ :=
    ((hL.1.add hK.1).div_const 2 |>.add (integrable_const (c ^ (2 * m)))).const_mul A
  have hb (x : E) : |L x * K x - c| ^ (2 * m) ≤ R x :=
    centered_product_even_power_bound (L x) (K x) c m
  have hI : Integrable (fun x => |L x * K x - c| ^ (2 * m)) μ := by
    refine hR.mono' (by fun_prop) (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact hb x
  refine ⟨hI, ?_⟩
  have hLP : Var[L; μ] ^ (2 * m) ≤ 1 := pow_le_one₀ (variance_nonneg L μ) hL1
  have hKP : Var[K; μ] ^ (2 * m) ≤ 1 := pow_le_one₀ (variance_nonneg K μ) hK1
  have hcP : c ^ (2 * m) ≤ 1 := by
    rw [← pow_abs_two_mul]
    exact pow_le_one₀ (abs_nonneg c) hc
  have hMoment := firstScoreMoment_nonneg (2 * m)
  have hRint : (∫ x, R x ∂μ) =
      A * ((Var[L; μ] ^ (2 * m) * firstScoreMoment (2 * m) +
        Var[K; μ] ^ (2 * m) * firstScoreMoment (2 * m)) / 2 + c ^ (2 * m)) := by
    unfold R
    rw [integral_const_mul]
    congr 1
    have hsum : Integrable (fun x => ((L x) ^ (4 * m) + (K x) ^ (4 * m)) / 2) μ := by
      convert! (hL.1.add hK.1).div_const 2 using 1
    have hAdd : (∫ x, (L x) ^ (4 * m) + (K x) ^ (4 * m) ∂μ) =
        (∫ x, (L x) ^ (4 * m) ∂μ) + ∫ x, (K x) ^ (4 * m) ∂μ := by
      convert! integral_add hL.1 hK.1 using 1
    calc
      _ = (∫ x, ((L x) ^ (4 * m) + (K x) ^ (4 * m)) / 2 ∂μ) +
          ∫ _ : E, c ^ (2 * m) ∂μ := by
        convert! integral_add hsum (integrable_const (c ^ (2 * m))) using 1
      _ = _ := by
        simp only [div_eq_mul_inv, integral_mul_const]
        rw [hAdd, hL.2, hK.2]
        simp
  calc
    _ ≤ ∫ x, R x ∂μ := integral_mono hI hR hb
    _ = _ := hRint
    _ ≤ _ := by
      have hLM := mul_le_mul_of_nonneg_right hLP hMoment
      have hKM := mul_le_mul_of_nonneg_right hKP hMoment
      dsimp only [A]
      nlinarith [show (0 : ℝ) ≤ 2 ^ (2 * m - 1) by positivity]

/-- Actual mixed covariance-score moments have the product of the physical
mean-score energy envelopes. No independence of the two projections, or
conditioning bound on the full Gaussian covariance, is required. -/
theorem gaussian_mixed_score_even_moment_bound (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) (hL0 : ∫ x, L x ∂μ = 0) (hK0 : ∫ x, K x ∂μ = 0)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hLA : Var[L; μ] ≤ A ^ 2) (hKB : Var[K; μ] ≤ B ^ 2) (m : ℕ) :
    Integrable (fun x => |L x * K x - cov[L, K; μ]| ^ (2 * m)) μ ∧
    (∫ x, |L x * K x - cov[L, K; μ]| ^ (2 * m) ∂μ) ≤
      (A * B) ^ (2 * m) * (2 ^ (2 * m - 1) * (firstScoreMoment (2 * m) + 1)) := by
  let L' : E →L[ℝ] ℝ := A⁻¹ • L
  let K' : E →L[ℝ] ℝ := B⁻¹ • K
  have hL'0 : ∫ x, L' x ∂μ = 0 := by
    change (∫ x, A⁻¹ * L x ∂μ) = 0
    rw [integral_const_mul, hL0, mul_zero]
  have hK'0 : ∫ x, K' x ∂μ = 0 := by
    change (∫ x, B⁻¹ * K x ∂μ) = 0
    rw [integral_const_mul, hK0, mul_zero]
  have hL'1 : Var[L'; μ] ≤ 1 := by
    change Var[fun x => A⁻¹ * L x; μ] ≤ 1
    rw [variance_const_mul]
    calc
      _ ≤ (A⁻¹) ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left hLA (sq_nonneg _)
      _ = 1 := by field_simp
  have hK'1 : Var[K'; μ] ≤ 1 := by
    change Var[fun x => B⁻¹ * K x; μ] ≤ 1
    rw [variance_const_mul]
    calc
      _ ≤ (B⁻¹) ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hKB (sq_nonneg _)
      _ = 1 := by field_simp
  have hc : cov[L', K'; μ] = A⁻¹ * B⁻¹ * cov[L, K; μ] := by
    change cov[fun x => A⁻¹ * L x, fun x => B⁻¹ * K x; μ] = _
    rw [covariance_const_mul_left, covariance_const_mul_right]
    ring
  have hpoint (x : E) : L x * K x - cov[L, K; μ] =
      (A * B) * (L' x * K' x - cov[L', K'; μ]) := by
    rw [hc]
    dsimp [L', K']
    simp only [smul_apply, smul_eq_mul]
    field_simp
  have hpower : (fun x => |L x * K x - cov[L, K; μ]| ^ (2 * m)) =
      fun x => (A * B) ^ (2 * m) * |L' x * K' x - cov[L', K'; μ]| ^ (2 * m) := by
    funext x
    rw [hpoint x, abs_mul, abs_of_pos (mul_pos hA hB), mul_pow]
  have h := gaussian_normalized_mixed_score_even_moment μ L' K' hL'0 hK'0 hL'1 hK'1 m
  rw [hpower]
  constructor
  · exact h.1.const_mul _
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h.2 (by positivity)

end MixedGaussianScores

section MixedGaussianDifferentiation

def weightedMeanTilt (v c l k t : ℝ) : ℝ :=
  (l - t * c) * Real.exp (t * k - t ^ 2 * v / 2)

def weightedMeanTiltDerivative (v c l k t : ℝ) : ℝ :=
  Real.exp (t * k - t ^ 2 * v / 2) * ((l - t * c) * (k - t * v) - c)

theorem hasDerivAt_weightedMeanTilt (v c l k t : ℝ) :
    HasDerivAt (weightedMeanTilt v c l k) (weightedMeanTiltDerivative v c l k t) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (s * k - s ^ 2 * v / 2))
      (Real.exp (t * k - t ^ 2 * v / 2) * (k - t * v)) t := by
    convert! (((hasDerivAt_id t).mul_const k).sub
      (((hasDerivAt_id t).pow 2).mul_const (v / 2))).exp using 1
    · funext s
      congr 1
      dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
      ring
    · dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
      ring_nf
  convert! (((hasDerivAt_const t l).sub ((hasDerivAt_id t).mul_const c)).mul he) using 1
  dsimp [weightedMeanTiltDerivative]
  ring

def weightedMeanTiltBound (v c l k : ℝ) : ℝ :=
  (|c| + (|l| + |c|) * (|k| + v)) * Real.exp |k|

theorem weightedMeanTilt_derivative_bound (v c l k t : ℝ) (hv : 0 ≤ v)
    (ht : |t| ≤ 1) :
    |weightedMeanTiltDerivative v c l k t| ≤ weightedMeanTiltBound v c l k := by
  have htc : |t * c| ≤ |c| := by rw [abs_mul]; nlinarith [abs_nonneg c]
  have htv : |t * v| ≤ v := by rw [abs_mul, abs_of_nonneg hv]; nlinarith
  have hl : |l - t * c| ≤ |l| + |c| := (abs_sub _ _).trans (by linarith)
  have hk : |k - t * v| ≤ |k| + v := (abs_sub _ _).trans (by linarith)
  have hexp : Real.exp (t * k - t ^ 2 * v / 2) ≤ Real.exp |k| := by
    apply Real.exp_le_exp.mpr
    have htk : t * k ≤ |k| := calc
      _ ≤ |t * k| := le_abs_self _
      _ = |t| * |k| := abs_mul _ _
      _ ≤ 1 * |k| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      _ = _ := one_mul _
    nlinarith [sq_nonneg t]
  have hpoly : |(l - t * c) * (k - t * v) - c| ≤
      (|l| + |c|) * (|k| + v) + |c| := by
    calc
      _ ≤ |(l - t * c) * (k - t * v)| + |c| := abs_sub _ _
      _ = |l - t * c| * |k - t * v| + |c| := by rw [abs_mul]
      _ ≤ _ := by nlinarith [mul_le_mul hl hk (abs_nonneg _) (by positivity)]
  dsimp only [weightedMeanTiltDerivative, weightedMeanTiltBound]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h := mul_le_mul hexp hpoly (abs_nonneg _) (Real.exp_nonneg |k|)
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] [SecondCountableTopology E] in
/-- Actual joint Gaussian moments supply the dominator for differentiating
a likelihood with a retained, possibly correlated, linear observation. -/
theorem integrable_weightedMeanTiltBound (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) (hK0 : ∫ x, K x ∂μ = 0) (v c : ℝ) :
    Integrable (fun x => weightedMeanTiltBound v c (L x) (K x)) μ := by
  let w : ℝ≥0 := (Var[K; μ]).toNNReal
  have hLaw : HasLaw K (gaussianReal 0 w) μ := by
    simpa only [hK0, sub_zero] using centered_projection_hasLaw μ K
  let H : ℝ → ℝ := fun z => (|z| + v) * Real.exp |z|
  have hHsq : Integrable (fun z => (H z) ^ 2) (gaussianReal 0 w) := by
    have h₀ := integrable_gaussian_abs_power_exp w 2 (by norm_num) 0
    have h₁ := integrable_gaussian_abs_power_exp w 2 (by norm_num) 1
    have h₂ := integrable_gaussian_abs_power_exp w 2 (by norm_num) 2
    convert! (h₂.add (h₁.const_mul (2 * v))).add (h₀.const_mul (v ^ 2)) using 1
    ext z
    have he : (Real.exp |z|) ^ 2 = Real.exp (2 * |z|) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    dsimp [H]
    rw [mul_pow, he]
    simp only [pow_zero, one_mul, pow_one]
    ring
  have hH₂ : MemLp (fun x => H (K x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by dsimp [H]; fun_prop)).mpr
    simpa only [Function.comp_def] using hLaw.integrable_comp hHsq
  have hH : Integrable (fun x => H (K x)) μ := hH₂.integrable (by norm_num)
  have hExp : Integrable (fun x => Real.exp |K x|) μ := by
    have h := integrable_gaussian_abs_power_exp w 1 (by norm_num) 0
    simp only [pow_zero, one_mul, one_mul] at h
    exact hLaw.integrable_comp h
  have hProd : Integrable (fun x => |L x| * H (K x)) μ := by
    convert! (IsGaussian.memLp_dual μ L 2 (by norm_num)).norm.integrable_mul hH₂ using 1
  convert! ((hExp.const_mul |c|).add hProd).add (hH.const_mul |c|) using 1
  ext x
  dsimp [weightedMeanTiltBound, H]
  ring

/-- Genuine mixed Gaussian mean differentiation for bounded rough tests.
The retained first score is differentiated under the actual Gaussian integral;
its cross covariance correction is derived, not assumed as a score identity. -/
theorem hasDerivAt_gaussian_weighted_mean_zero (μ : Measure E) [IsGaussian μ]
    (L K : E →L[ℝ] ℝ) (hK0 : ∫ x, K x ∂μ = 0)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    HasDerivAt (fun s : ℝ => ∫ y, F (y + s • covarianceResponse μ K) * L y ∂μ)
      (∫ y, F y * (L y * K y - cov[L, K; μ]) ∂μ) 0 := by
  let v : ℝ := Var[K; μ]
  let c : ℝ := cov[L, K; μ]
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hB 0)
  have hFint : Integrable (fun y => F y * L y) μ := by
    convert! (IsGaussian.integrable_dual μ L).bdd_mul hF.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x)) using 1
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := (0 : ℝ)) (s := Metric.ball 0 1)
    (F := fun t x => F x * weightedMeanTilt v c (L x) (K x) t)
    (F' := fun t x => F x * weightedMeanTiltDerivative v c (L x) (K x) t)
    (bound := fun x => M * weightedMeanTiltBound v c (L x) (K x))
    (Metric.ball_mem_nhds 0 (by norm_num))
    (Filter.Eventually.of_forall (fun t => by unfold weightedMeanTilt; fun_prop))
    (by simpa [weightedMeanTilt] using hFint)
    (by unfold weightedMeanTiltDerivative; fun_prop)
    (Filter.Eventually.of_forall (fun x t ht => by
      have ht' : |t| ≤ 1 := by
        have hh : |t| < 1 := by
          simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
        exact hh.le
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB x)
        (weightedMeanTilt_derivative_bound v c (L x) (K x) t (variance_nonneg K μ) ht')
        (abs_nonneg _) hM))
    ((integrable_weightedMeanTiltBound μ L K hK0 v c).const_mul M)
    (Filter.Eventually.of_forall (fun x t _ =>
      (hasDerivAt_weightedMeanTilt v c (L x) (K x) t).const_mul (F x)))
  have hfun : (fun t : ℝ => ∫ x, F x * weightedMeanTilt v c (L x) (K x) t ∂μ) =
      fun s : ℝ => ∫ y, F (y + s • covarianceResponse μ K) * L y ∂μ := by
    funext s
    convert! (gaussian_weighted_mean_likelihood μ L K hK0 F hF s).symm using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only [weightedMeanTilt, v, c]
      ring)
  rw [hfun] at h
  simpa [weightedMeanTiltDerivative, v, c] using h.2

/-- An actual mixed second directional mean derivative against a bounded
measurable rough test. Both directions are physical covariance responses,
and the output is the actual mixed covariance Hermite score. -/
theorem hasDerivAt_gaussian_mixed_mean_derivative_zero
    (μ : Measure E) [IsGaussian μ] (L K : E →L[ℝ] ℝ)
    (hL0 : ∫ x, L x ∂μ = 0) (hK0 : ∫ x, K x ∂μ = 0)
    (hLVar : 0 < Var[L; μ]) (F : E → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      ∫ y, F (y + s • covarianceResponse μ L + t • covarianceResponse μ K) ∂μ) 0)
      (∫ y, F y * (L y * K y - cov[L, K; μ]) ∂μ) 0 := by
  have heq : (fun t : ℝ => deriv (fun s : ℝ =>
      ∫ y, F (y + s • covarianceResponse μ L + t • covarianceResponse μ K) ∂μ) 0) =
      fun t : ℝ => ∫ y, F (y + t • covarianceResponse μ K) * L y ∂μ := by
    funext t
    have h := hasDerivAt_gaussian_covarianceResponse_mean μ L hL0 hLVar
      (fun y => F (y + t • covarianceResponse μ K)) (by fun_prop) M (fun y => hB _) 0
    simpa only [zero_smul, add_zero] using h.deriv
  rw [heq]
  exact hasDerivAt_gaussian_weighted_mean_zero μ L K hK0 F hF M hB

end MixedGaussianDifferentiation

section SignedCovarianceFamilies

theorem integral_gaussian_prod_density (v w : ℝ) (hv : 0 < v) (hw : 0 < w)
    (F : ℝ × ℝ → ℝ) :
    (∫ z, F z ∂(gaussianReal 0 v.toNNReal).prod (gaussianReal 0 w.toNNReal)) =
      ∫ z, F z * varianceDensity v z.1 * varianceDensity w z.2
        ∂(volume : Measure ℝ).prod volume := by
  rw [gaussianReal_of_var_ne_zero 0 (by positivity : v.toNNReal ≠ 0),
    gaussianReal_of_var_ne_zero 0 (by positivity : w.toNNReal ≠ 0),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun z => by
        exact lt_top_iff_ne_top.mpr
          (ENNReal.mul_ne_top (gaussianPDF_lt_top.ne) (gaussianPDF_lt_top.ne))))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [ENNReal.toReal_mul]
    simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]
    rw [varianceDensity_eq_pdf hv, varianceDensity_eq_pdf hw]
    ring)

def varianceDensityDerivative (w z : ℝ) : ℝ :=
  varianceDensity w z * (z ^ 2 - w) / (2 * w ^ 2)

theorem integrable_varianceDensity (v : ℝ) (hv : 0 < v) :
    Integrable (varianceDensity v) volume := by
  simpa only [mul_one] using integrable_varianceDensity_mul v hv
    (fun _ => (1 : ℝ)) (integrable_const 1)

/-- Two independently reserved Gaussian variance coordinates may carry
arbitrary signed affine covariance changes. This is a genuine derivative of
the actual Gaussian product-law expectation for a bounded rough joint test. -/
theorem hasDerivAt_gaussian_two_signed_variances (v w e f : ℝ)
    (hv : 0 < v) (hw : 0 < w) (F : ℝ × ℝ → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ z, |F z| ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ z, F z
      ∂(gaussianReal 0 (v + t * e).toNNReal).prod
        (gaussianReal 0 (w + t * f).toNNReal))
      ((1 / 2 : ℝ) * ∫ z, F z *
        (e * secondScore v.toNNReal z.1 + f * secondScore w.toNNReal z.2)
          ∂(gaussianReal 0 v.toNNReal).prod (gaussianReal 0 w.toNNReal)) 0 := by
  let S : Set ℝ := {t | v / 2 < v + t * e ∧ v + t * e < 2 * v ∧
    w / 2 < w + t * f ∧ w + t * f < 2 * w}
  have hS : S ∈ nhds (0 : ℝ) := by
    have h₁ : ∀ᶠ t in nhds (0 : ℝ), v / 2 < v + t * e ∧ v + t * e < 2 * v := by
      simpa using (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually
        (Ioo_mem_nhds (show v / 2 < v + 0 * e by linarith)
          (show v + 0 * e < 2 * v by linarith))
    have h₂ : ∀ᶠ t in nhds (0 : ℝ), w / 2 < w + t * f ∧ w + t * f < 2 * w := by
      simpa using (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually
        (Ioo_mem_nhds (show w / 2 < w + 0 * f by linarith)
          (show w + 0 * f < 2 * w by linarith))
    filter_upwards [h₁, h₂] with t ht₁ ht₂
    exact ⟨ht₁.1, ht₁.2, ht₂.1, ht₂.2⟩
  have hM : 0 ≤ M := (abs_nonneg (F (0, 0))).trans (hB (0, 0))
  let B : ℝ × ℝ → ℝ := fun z => M *
    (2 * |e| * varianceDerivativeBound v 1 z.1 * varianceDensity (2 * w) z.2 +
      2 * |f| * varianceDensity (2 * v) z.1 * varianceDerivativeBound w 1 z.2)
  have hBI : Integrable B ((volume : Measure ℝ).prod volume) := by
    have h₁ := (integrable_varianceDerivativeBound v hv 1).mul_prod
      (integrable_varianceDensity (2 * w) (by positivity))
    have h₂ := (integrable_varianceDensity (2 * v) (by positivity)).mul_prod
      (integrable_varianceDerivativeBound w hw 1)
    convert! ((h₁.const_mul (2 * |e|)).add (h₂.const_mul (2 * |f|))).const_mul M using 1
    ext z
    dsimp [B]
    ring
  have hDI : Integrable (fun z : ℝ × ℝ =>
      F z * varianceDensity v z.1 * varianceDensity w z.2)
      ((volume : Measure ℝ).prod volume) := by
    convert! ((integrable_varianceDensity v hv).mul_prod
      (integrable_varianceDensity w hw)).bdd_mul hF.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB z)) using 1
    ext z
    ring
  have hder (z : ℝ × ℝ) (t : ℝ) (ht : t ∈ S) :
      HasDerivAt (fun t : ℝ => F z * varianceDensity (v + t * e) z.1 *
        varianceDensity (w + t * f) z.2)
        (F z * (e * varianceDensityDerivative (v + t * e) z.1 *
          varianceDensity (w + t * f) z.2 + f * varianceDensity (v + t * e) z.1 *
          varianceDensityDerivative (w + t * f) z.2)) t := by
    have hv' : 0 < v + t * e := by have := ht.1; dsimp [S] at ht; linarith [ht.1]
    have hw' : 0 < w + t * f := by dsimp [S] at ht; linarith [ht.2.2.1]
    have h₁ := (hasDerivAt_varianceDensity hv' z.1).comp t
      ((hasDerivAt_const t v).add ((hasDerivAt_id t).mul_const e))
    have h₂ := (hasDerivAt_varianceDensity hw' z.2).comp t
      ((hasDerivAt_const t w).add ((hasDerivAt_id t).mul_const f))
    convert! (h₁.const_mul (F z)).mul h₂ using 1
    dsimp only [varianceDensityDerivative, Function.comp_def, Pi.mul_apply, Pi.add_apply, id_eq]
    ring
  have hbound (z : ℝ × ℝ) (t : ℝ) (ht : t ∈ S) :
      ‖F z * (e * varianceDensityDerivative (v + t * e) z.1 *
          varianceDensity (w + t * f) z.2 + f * varianceDensity (v + t * e) z.1 *
          varianceDensityDerivative (w + t * f) z.2)‖ ≤ B z := by
    dsimp [S] at ht
    have hv' : 0 < v + t * e := by linarith [ht.1]
    have hw' : 0 < w + t * f := by linarith [ht.2.2.1]
    have hd₁ : |varianceDensityDerivative (v + t * e) z.1| ≤
        varianceDerivativeBound v 1 z.1 := by
      simpa only [varianceDensityDerivative, one_mul, Real.norm_eq_abs] using
        varianceDensity_derivative_bound hv ht.1.le ht.2.1.le (fun _ => (1 : ℝ)) 1
          (by norm_num) (fun _ => by simp) z.1
    have hd₂ : |varianceDensityDerivative (w + t * f) z.2| ≤
        varianceDerivativeBound w 1 z.2 := by
      simpa only [varianceDensityDerivative, one_mul, Real.norm_eq_abs] using
        varianceDensity_derivative_bound hw ht.2.2.1.le ht.2.2.2.le (fun _ => (1 : ℝ)) 1
          (by norm_num) (fun _ => by simp) z.2
    have hp₁ := varianceDensity_le_broader hv ht.1.le ht.2.1.le z.1
    have hp₂ := varianceDensity_le_broader hw ht.2.2.1.le ht.2.2.2.le z.2
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ M * (|e * varianceDensityDerivative (v + t * e) z.1 *
          varianceDensity (w + t * f) z.2| + |f * varianceDensity (v + t * e) z.1 *
          varianceDensityDerivative (w + t * f) z.2|) :=
        mul_le_mul (hB z) (abs_add_le _ _) (abs_nonneg _) hM
      _ ≤ B z := by
        simp only [abs_mul, abs_of_pos (varianceDensity_pos hv' z.1),
          abs_of_pos (varianceDensity_pos hw' z.2)]
        have hP₁ := (varianceDensity_pos (show 0 < 2 * v by positivity) z.1).le
        have hP₂ := (varianceDensity_pos (show 0 < 2 * w by positivity) z.2).le
        have hD₁ : 0 ≤ varianceDerivativeBound v 1 z.1 := by
          dsimp [varianceDerivativeBound]; positivity
        have hD₂ : 0 ≤ varianceDerivativeBound w 1 z.2 := by
          dsimp [varianceDerivativeBound]; positivity
        calc
          _ ≤ M * (|e| * varianceDerivativeBound v 1 z.1 *
              (2 * varianceDensity (2 * w) z.2) + |f| *
              (2 * varianceDensity (2 * v) z.1) * varianceDerivativeBound w 1 z.2) := by
            gcongr
            exact (varianceDensity_pos hw' z.2).le
          _ = B z := by dsimp [B]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ).prod volume) (x₀ := (0 : ℝ)) (s := S)
    (F := fun t z => F z * varianceDensity (v + t * e) z.1 * varianceDensity (w + t * f) z.2)
    (F' := fun t z => F z * (e * varianceDensityDerivative (v + t * e) z.1 *
      varianceDensity (w + t * f) z.2 + f * varianceDensity (v + t * e) z.1 *
      varianceDensityDerivative (w + t * f) z.2))
    (bound := B) hS
    (Filter.Eventually.of_forall (fun t => by unfold varianceDensity; fun_prop))
    (by simpa using hDI)
    (by unfold varianceDensityDerivative varianceDensity; fun_prop)
    (Filter.Eventually.of_forall hbound) hBI
    (Filter.Eventually.of_forall hder)
  have hcoeff : (∫ z : ℝ × ℝ, F z * (e * varianceDensityDerivative v z.1 *
      varianceDensity w z.2 + f * varianceDensity v z.1 * varianceDensityDerivative w z.2)
        ∂(volume : Measure ℝ).prod volume) =
      (1 / 2 : ℝ) * ∫ z, F z * (e * secondScore v.toNNReal z.1 +
        f * secondScore w.toNNReal z.2)
          ∂(gaussianReal 0 v.toNNReal).prod (gaussianReal 0 w.toNNReal) := by
    rw [integral_gaussian_prod_density v w hv hw, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only [varianceDensityDerivative, secondScore]
      rw [Real.coe_toNNReal _ hv.le, Real.coe_toNNReal _ hw.le]
      ring)
  have hh := h.2
  simp only [zero_mul, add_zero] at hh
  rw [hcoeff] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hS] with t ht
  dsimp [S] at ht
  exact integral_gaussian_prod_density (v + t * e) (w + t * f)
    (by linarith [ht.1]) (by linarith [ht.2.2.1]) F

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def twoReserveGaussianLaw (ν : Measure E) (d₁ d₂ : E) (v w : ℝ≥0) : Measure E :=
  rankOneGaussianLaw (rankOneGaussianLaw ν d₁ v) d₂ w

instance twoReserveGaussianLaw_isGaussian (ν : Measure E) [IsGaussian ν]
    (d₁ d₂ : E) (v w : ℝ≥0) : IsGaussian (twoReserveGaussianLaw ν d₁ d₂ v w) := by
  unfold twoReserveGaussianLaw
  infer_instance

def twoReserveAverage (ν : Measure E) (d₁ d₂ : E) (F : E → ℝ) (z : ℝ × ℝ) : ℝ :=
  ∫ x, F (x + z.1 • d₁ + z.2 • d₂) ∂ν

theorem measurable_twoReserveAverage (ν : Measure E) [IsProbabilityMeasure ν]
    (d₁ d₂ : E) (F : E → ℝ) (hF : Measurable F) :
    Measurable (twoReserveAverage ν d₁ d₂ F) := by
  have h : Measurable (fun p : (ℝ × ℝ) × E =>
      F (p.2 + p.1.1 • d₁ + p.1.2 • d₂)) := by fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

omit [BorelSpace E] [SecondCountableTopology E] in
theorem twoReserveAverage_bound (ν : Measure E) [IsProbabilityMeasure ν]
    (d₁ d₂ : E) (F : E → ℝ) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (z : ℝ × ℝ) :
    |twoReserveAverage ν d₁ d₂ F z| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x => F (x + z.1 • d₁ + z.2 • d₂)) (C := M)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB _))
  simpa only [twoReserveAverage, Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem integral_twoReserveGaussianLaw (ν : Measure E) [IsProbabilityMeasure ν]
    (d₁ d₂ : E) (v w : ℝ≥0) (F : E → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    (∫ y, F y ∂twoReserveGaussianLaw ν d₁ d₂ v w) =
      ∫ z, twoReserveAverage ν d₁ d₂ F z ∂(gaussianReal 0 v).prod (gaussianReal 0 w) := by
  have hAvg : Integrable (twoReserveAverage ν d₁ d₂ F)
      ((gaussianReal 0 v).prod (gaussianReal 0 w)) :=
    (integrable_const M).mono' (measurable_twoReserveAverage ν d₁ d₂ F hF).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs] using twoReserveAverage_bound ν d₁ d₂ F M hB z))
  rw [twoReserveGaussianLaw, integral_rankOneGaussianLaw _ d₂ w F hF M hB,
    integral_prod_symm _ hAvg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z₂ => by
    dsimp only [rankOneAverage]
    rw [integral_rankOneGaussianLaw ν d₁ v (fun y => F (y + z₂ • d₂))
      (by fun_prop) M (fun y => hB _)]
    rfl)

/-- Signed covariance differentiation of an actual physical Gaussian output
with two independent scalar reserves and an arbitrary Gaussian residual. The
score lives on the unchanged reserved fractions, exactly as in the word split. -/
theorem hasDerivAt_twoReserveGaussianLaw (ν : Measure E) [IsProbabilityMeasure ν]
    (d₁ d₂ : E) (v w e f : ℝ) (hv : 0 < v) (hw : 0 < w)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ y, F y ∂twoReserveGaussianLaw ν d₁ d₂
      (v + t * e).toNNReal (w + t * f).toNNReal)
      ((1 / 2 : ℝ) * ∫ z, twoReserveAverage ν d₁ d₂ F z *
        (e * secondScore v.toNNReal z.1 + f * secondScore w.toNNReal z.2)
          ∂(gaussianReal 0 v.toNNReal).prod (gaussianReal 0 w.toNNReal)) 0 := by
  have h := hasDerivAt_gaussian_two_signed_variances v w e f hv hw
    (twoReserveAverage ν d₁ d₂ F) (measurable_twoReserveAverage ν d₁ d₂ F hF)
    M (twoReserveAverage_bound ν d₁ d₂ F M hB)
  convert! h using 1
  funext t
  exact integral_twoReserveGaussianLaw ν d₁ d₂ _ _ F hF M hB

omit [SecondCountableTopology E] in
/-- The above family changes actual physical covariance by precisely its
signed rank-one sum; no matrix square root is differentiated. -/
theorem variance_twoReserveGaussianLaw_affine [CompleteSpace E]
    (ν : Measure E) [IsGaussian ν] (d₁ d₂ : E) (v w e f t : ℝ)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hvt : 0 ≤ v + t * e) (hwt : 0 ≤ w + t * f)
    (K : E →L[ℝ] ℝ) :
    Var[K; twoReserveGaussianLaw ν d₁ d₂ (v + t * e).toNNReal (w + t * f).toNNReal] =
      Var[K; twoReserveGaussianLaw ν d₁ d₂ v.toNNReal w.toNNReal] +
        t * (e * (K d₁) ^ 2 + f * (K d₂) ^ 2) := by
  simp only [twoReserveGaussianLaw, variance_rankOneGaussianLaw,
    Real.coe_toNNReal _ hv, Real.coe_toNNReal _ hw,
    Real.coe_toNNReal _ hvt, Real.coe_toNNReal _ hwt]
  ring

/-- Two fixed positive reserves carry a genuine signed symmetric cross
covariance direction through the physical directions a+b and a-b. -/
theorem hasDerivAt_twoReserve_cross_covariance (ν : Measure E) [IsProbabilityMeasure ν]
    (a b : E) (v w : ℝ) (hv : 0 < v) (hw : 0 < w)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ y, F y ∂twoReserveGaussianLaw ν (a + b) (a - b)
      (v + t * (1 / 2)).toNNReal (w + t * (-1 / 2)).toNNReal)
      ((1 / 4 : ℝ) * ∫ z, twoReserveAverage ν (a + b) (a - b) F z *
        (secondScore v.toNNReal z.1 - secondScore w.toNNReal z.2)
          ∂(gaussianReal 0 v.toNNReal).prod (gaussianReal 0 w.toNNReal)) 0 := by
  have h := hasDerivAt_twoReserveGaussianLaw ν (a + b) (a - b) v w
    (1 / 2) (-1 / 2) hv hw F hF M hB
  convert! h using 1
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by dsimp only; ring)

omit [SecondCountableTopology E] in
theorem variance_twoReserve_cross_covariance [CompleteSpace E]
    (ν : Measure E) [IsGaussian ν] (a b : E) (v w t : ℝ)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hvt : 0 ≤ v + t * (1 / 2))
    (hwt : 0 ≤ w + t * (-1 / 2)) (K : E →L[ℝ] ℝ) :
    Var[K; twoReserveGaussianLaw ν (a + b) (a - b)
      (v + t * (1 / 2)).toNNReal (w + t * (-1 / 2)).toNNReal] =
      Var[K; twoReserveGaussianLaw ν (a + b) (a - b) v.toNNReal w.toNNReal] +
        2 * t * K a * K b := by
  have h := variance_twoReserveGaussianLaw_affine ν (a + b) (a - b) v w
    (1 / 2) (-1 / 2) t hv hw hvt hwt K
  convert! h using 1
  rw [map_add, map_sub]
  ring

end SignedCovarianceFamilies

/-- Suppress the old increment only in the root.  The subtracted term is
independent of that increment and therefore vanishes against the old score. -/
theorem secondScore_center_root (v : ℝ≥0) (f : ℝ → ℝ) (m : ℝ)
    (hf : Integrable (fun z => secondScore v z * f (m + z)) (gaussianReal 0 v)) :
    (∫ z, secondScore v z * (f (m + z) - f m) ∂gaussianReal 0 v) =
      ∫ z, secondScore v z * f (m + z) ∂gaussianReal 0 v := by
  have hc := (integrable_secondScore v).mul_const (f m)
  simp_rw [mul_sub]
  rw [integral_sub hf hc, integral_mul_const, integral_secondScore]
  simp

/-- Bounded continuous band tests satisfy the integrability side condition. -/
theorem integrable_secondScore_root (v : ℝ≥0) (f : ℝ → ℝ) (m A : ℝ)
    (hf : Continuous f) (hA : ∀ x, |f x| ≤ A) :
    Integrable (fun z => secondScore v z * f (m + z)) (gaussianReal 0 v) := by
  refine (integrable_secondScore v).mul_bdd (c := A) ?_ ?_
  · exact (hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hA (m + z))

/-- Two independent scalar Gaussian fractions: an old covariance score and a
new mean score.  This is the algebraic `n=1` native word before heat weights. -/
def nativeFirstWord (u v : ℝ≥0) (f a : ℝ → ℝ) (c mH mS ρ : ℝ) : ℝ :=
  ∫ w, firstScore u w * (a (mS + w) - c) *
    (∫ z, secondScore v z * f (mH + ρ * w + z) ∂gaussianReal 0 v)
    ∂gaussianReal 0 u

/-- A new independent first score leaves the exact old root centering intact. -/
theorem nativeFirstWord_center_root (u v : ℝ≥0) (f a : ℝ → ℝ)
    (c mH mS ρ A : ℝ) (hf : Continuous f) (hA : ∀ x, |f x| ≤ A) :
    nativeFirstWord u v f a c mH mS ρ =
      ∫ w, firstScore u w * (a (mS + w) - c) *
        (∫ z, secondScore v z *
          (f (mH + ρ * w + z) - f (mH + ρ * w)) ∂gaussianReal 0 v)
        ∂gaussianReal 0 u := by
  unfold nativeFirstWord
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by
    dsimp only
    rw [secondScore_center_root v f (mH + ρ * w)
      (integrable_secondScore_root v f (mH + ρ * w) A hf hA)])

section FiniteHistoryLeverage
open SHE.StoppedFourier Set
open scoped InnerProductSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The time leverage density of an orthonormal finite family in the actual
stopped-history range. It uses the physical heat histories, not a matrix inverse. -/
def historyLeverage (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (u : ℝ) : ℝ :=
  ∑ k, ‖historyF Finset.univ (z k) σ target center u‖ ^ 2

theorem historyLeverage_nonneg (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (u : ℝ) : 0 ≤ historyLeverage z σ target center u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem historyLeverage_measurable (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) :
    Measurable (historyLeverage z σ target center) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact historyF_norm_sq_measurable Finset.univ (z k) σ target center (fun i _ => hages i)

theorem historyLeverage_integrable (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    Integrable (historyLeverage z σ target center) (volume.restrict (Ici q)) := by
  apply integrable_finsetSum
  intro k _
  have hm := historyF_memLp_time Finset.univ (z k) σ target center (fun i _ => hages i) q
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

/-- The total leverage is the actual number of orthonormal covariance-range
directions, including singular and colliding observation configurations. -/
theorem integral_historyLeverage (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) (q : ℝ)
    (horth : Orthonormal ℂ (fun k => historyTimeVector Finset.univ (z k)
      σ target center (fun i _ => hages i) q)) :
    (∫ u in Ici q, historyLeverage z σ target center u) = Fintype.card κ := by
  change (∫ u in Ici q, ∑ k, ‖historyF Finset.univ (z k) σ target center u‖ ^ 2) = _
  rw [integral_finsetSum]
  · have he : ∀ k, (∫ u in Ici q,
        ‖historyF Finset.univ (z k) σ target center u‖ ^ 2) = 1 := by
      intro k
      rw [← toLp_norm_sq_eq_integral
        (historyF_memLp_time Finset.univ (z k) σ target center (fun i _ => hages i) q)]
      change ‖historyTimeVector Finset.univ (z k) σ target center (fun i _ => hages i) q‖ ^ 2 = 1
      rw [horth.norm_eq_one k, one_pow]
    simp_rw [he]
    simp
  · intro k _
    have hm := historyF_memLp_time Finset.univ (z k) σ target center (fun i _ => hages i) q
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

theorem historyLeverage_rank_bound (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) (q : ℝ)
    (horth : Orthonormal ℂ (fun k => historyTimeVector Finset.univ (z k)
      σ target center (fun i _ => hages i) q)) : Fintype.card κ ≤ Fintype.card ι := by
  have hl : LinearIndependent ℂ z := LinearIndependent.of_comp
    (historyLinearMap Finset.univ σ target center (fun i _ => hages i) q) horth.linearIndependent
  simpa using hl.fintype_card_le_finrank

/-- The early-time leverage bound follows from the actual stopped heat
semigroup and the full history norm. No condition number occurs. -/
theorem historyLeverage_early_bound (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) {q s u : ℝ}
    (hs : 0 < s) (hstop : ∀ i, q + s ≤ σ i)
    (hu : u ∈ Icc q (q + s / 2))
    (horth : Orthonormal ℂ (fun k => historyTimeVector Finset.univ (z k)
      σ target center (fun i _ => hages i) q)) :
    historyLeverage z σ target center u ≤ (4 / s) * Fintype.card κ := by
  have he : ∀ k, ‖historyF Finset.univ (z k) σ target center u‖ ^ 2 ≤ 4 / s := by
    intro k
    have hb := stopped_current_row_bound Finset.univ (z k) σ target center
      (fun i _ => hages i) (show 0 < s / 2 by positivity)
      (q := u) (fun i _ => by linarith [hstop i, hu.2])
    have hfin := (full_stopped_history_contraction Finset.univ (z k) σ target center
      (q := q) (Λ := 1) (by norm_num) (fun i _ => hages i)).2.1
    have hmono := ENNReal.toReal_mono hfin.ne
      (fullPhysicalEnergy_mono (H := historyF Finset.univ (z k) σ target center) hu.1)
    have hunit : (fullPhysicalEnergy (historyF Finset.univ (z k) σ target center) q).toReal = 1 := by
      rw [← historyTimeVector_norm_sq Finset.univ (z k) σ target center (fun i _ => hages i) q,
        horth.norm_eq_one k, one_pow]
    rw [hunit] at hmono
    have hh := hb.trans (mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 2 / (s / 2)))
    convert hh using 1
    field_simp
    ring
  calc
    _ ≤ ∑ _k : κ, (4 / s) := Finset.sum_le_sum (fun k _ => he k)
    _ = _ := by simp [mul_comm]

/-- A genuine weighted leverage estimate. The only hypotheses on the time
weight are local integrability before half the first stopping age and a uniform
bound afterwards; the physical leverage estimates are proved above. -/
theorem weighted_historyLeverage_bound (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) {q s M : ℝ}
    (hs : 0 < s) (hstop : ∀ i, q + s ≤ σ i)
    (horth : Orthonormal ℂ (fun k => historyTimeVector Finset.univ (z k)
      σ target center (fun i _ => hages i) q))
    (w : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ u, q ≤ u → 0 ≤ w u)
    (hwi : IntegrableOn w (Icc q (q + s / 2))) (hM : 0 ≤ M)
    (hwtail : ∀ u, q + s / 2 < u → w u ≤ M) :
    Integrable (fun u => w u * historyLeverage z σ target center u) (volume.restrict (Ici q)) ∧
    (∫ u in Ici q, w u * historyLeverage z σ target center u) ≤
      ((4 / s) * Fintype.card κ) * (∫ u in Icc q (q + s / 2), w u) +
        M * Fintype.card κ := by
  let A := Icc q (q + s / 2)
  let B : ℝ := (4 / s) * Fintype.card κ
  let ell := historyLeverage z σ target center
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : Integrable ell (volume.restrict (Ici q)) :=
    historyLeverage_integrable z σ target center hages q
  have hAi : Integrable (A.indicator w) (volume.restrict (Ici q)) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr hwi).restrict
  have hdom : Integrable (fun u => B * A.indicator w u + M * ell u)
      (volume.restrict (Ici q)) := (hAi.const_mul B).add (hL.const_mul M)
  have he : ∀ᵐ u ∂volume.restrict (Ici q), w u * ell u ≤
      B * A.indicator w u + M * ell u := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hL0 := historyLeverage_nonneg z σ target center u
    by_cases hA : u ∈ A
    · rw [Set.indicator_of_mem hA]
      have hb := historyLeverage_early_bound z σ target center hages hs hstop hA horth
      have hh := mul_le_mul_of_nonneg_left hb (hw0 u hu)
      have hm := mul_nonneg hM hL0
      dsimp only [ell, B] at *
      nlinarith
    · rw [Set.indicator_of_notMem hA, mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_right (hwtail u (by
        dsimp [A] at hA
        simp only [mem_Icc, not_and] at hA
        exact lt_of_not_ge (hA hu))) hL0
  have hprod : Integrable (fun u => w u * ell u) (volume.restrict (Ici q)) := by
    apply hdom.mono_nonneg
    · exact (hw.mul (historyLeverage_measurable z σ target center hages)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      exact mul_nonneg (hw0 u hu) (historyLeverage_nonneg z σ target center u)
    · exact he
  refine ⟨hprod, (integral_mono_ae hprod hdom he).trans_eq ?_⟩
  rw [integral_add (hAi.const_mul B) (hL.const_mul M), integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hset : A ∩ Ici q = A := Set.inter_eq_left.mpr (fun u hu => hu.1)
  rw [hset, integral_historyLeverage z σ target center hages q horth]

/-- The manuscript's negative time-power leverage estimate, for the genuine
full stopped-history frame, with an explicit constant and actual integrability. -/
theorem rpow_historyLeverage_bound (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) {s α : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α < 0) (hstop : ∀ i, s ≤ σ i)
    (horth : Orthonormal ℂ (fun k => historyTimeVector Finset.univ (z k)
      σ target center (fun i _ => hages i) 0)) :
    Integrable (fun u => u ^ α * historyLeverage z σ target center u)
      (volume.restrict (Ici 0)) ∧
    (∫ u in Ici 0, u ^ α * historyLeverage z σ target center u) ≤
      (Fintype.card κ : ℝ) * (s / 2) ^ α * (1 + 2 / (α + 1)) := by
  have hs2 : 0 < s / 2 := by positivity
  have hi : IntegrableOn (fun u : ℝ => u ^ α) (Icc 0 (s / 2)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegral.intervalIntegrable_rpow' hα (a := 0) (b := s / 2)).1
  have he := weighted_historyLeverage_bound z σ target center hages (q := 0) hs
    (fun i => by simpa using hstop i) horth (fun u : ℝ => u ^ α)
    (measurable_id.pow_const α) (fun u hu => Real.rpow_nonneg hu α)
    (by simpa only [zero_add] using hi) (Real.rpow_nonneg hs2.le α)
    (fun u hu => Real.rpow_le_rpow_of_nonpos hs2 (by linarith) hα0.le)
  have hn : α + 1 ≠ 0 := by linarith
  have hint : (∫ u in Icc (0 : ℝ) (s / 2), u ^ α) =
      (s / 2) ^ (α + 1) / (α + 1) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs2.le,
      integral_rpow (Or.inl hα), Real.zero_rpow hn, sub_zero]
  refine ⟨he.1, he.2.trans_eq ?_⟩
  simp only [zero_add, hint]
  rw [Real.rpow_add hs2, Real.rpow_one]
  field_simp
  ring

/-- The exact trace identity also applies to frames normalized by a larger
covariance: their reference trace is the sum of their genuine history energies. -/
theorem integral_historyLeverage_energy (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    (∫ u in Ici q, historyLeverage z σ target center u) =
      ∑ k, ‖historyTimeVector Finset.univ (z k) σ target center (fun i _ => hages i) q‖ ^ 2 := by
  change (∫ u in Ici q, ∑ k, ‖historyF Finset.univ (z k) σ target center u‖ ^ 2) = _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    exact (toLp_norm_sq_eq_integral
      (historyF_memLp_time Finset.univ (z k) σ target center (fun i _ => hages i) q)).symm
  · intro k _
    have hm := historyF_memLp_time Finset.univ (z k) σ target center (fun i _ => hages i) q
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

theorem historyLeverage_early_energy_bound (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) {q s u : ℝ}
    (hs : 0 < s) (hstop : ∀ i, q + s ≤ σ i) (hu : u ∈ Icc q (q + s / 2)) :
    historyLeverage z σ target center u ≤ (4 / s) *
      ∑ k, ‖historyTimeVector Finset.univ (z k) σ target center (fun i _ => hages i) q‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hb := stopped_current_row_bound Finset.univ (z k) σ target center
    (fun i _ => hages i) (show 0 < s / 2 by positivity)
    (q := u) (fun i _ => by linarith [hstop i, hu.2])
  have hfin := (full_stopped_history_contraction Finset.univ (z k) σ target center
    (q := q) (Λ := 1) (by norm_num) (fun i _ => hages i)).2.1
  have hmono := ENNReal.toReal_mono hfin.ne
    (fullPhysicalEnergy_mono (H := historyF Finset.univ (z k) σ target center) hu.1)
  have hh := hb.trans (mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 2 / (s / 2)))
  rw [← historyTimeVector_norm_sq Finset.univ (z k) σ target center (fun i _ => hages i) q] at hh
  convert hh using 1
  field_simp
  ring

/-- Positive time-weight integration from a finite total mass and the early
heat-semigroup bound. Every measurability and integrability condition is explicit. -/
theorem weighted_density_bound (ell w : ℝ → ℝ) {q s R M : ℝ} (_hs : 0 < s)
    (_hR : 0 ≤ R) (hM : 0 ≤ M) (hm : Measurable ell)
    (hi : Integrable ell (volume.restrict (Ici q))) (h0 : ∀ u, 0 ≤ ell u)
    (hmass : (∫ u in Ici q, ell u) ≤ R)
    (hearly : ∀ u ∈ Icc q (q + s / 2), ell u ≤ (4 / s) * R)
    (hw : Measurable w) (hw0 : ∀ u, q ≤ u → 0 ≤ w u)
    (hwi : IntegrableOn w (Icc q (q + s / 2)))
    (hwtail : ∀ u, q + s / 2 < u → w u ≤ M) :
    Integrable (fun u => w u * ell u) (volume.restrict (Ici q)) ∧
    (∫ u in Ici q, w u * ell u) ≤
      ((4 / s) * R) * (∫ u in Icc q (q + s / 2), w u) + M * R := by
  let A := Icc q (q + s / 2)
  let B : ℝ := (4 / s) * R
  have hAi : Integrable (A.indicator w) (volume.restrict (Ici q)) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr hwi).restrict
  have hdom : Integrable (fun u => B * A.indicator w u + M * ell u)
      (volume.restrict (Ici q)) := (hAi.const_mul B).add (hi.const_mul M)
  have he : ∀ᵐ u ∂volume.restrict (Ici q), w u * ell u ≤
      B * A.indicator w u + M * ell u := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    by_cases hA : u ∈ A
    · rw [Set.indicator_of_mem hA]
      have hh := mul_le_mul_of_nonneg_left (hearly u hA) (hw0 u hu)
      have ht := mul_nonneg hM (h0 u)
      dsimp only [B] at *
      nlinarith
    · rw [Set.indicator_of_notMem hA, mul_zero, zero_add]
      apply mul_le_mul_of_nonneg_right (hwtail u _) (h0 u)
      dsimp [A] at hA
      simp only [mem_Icc, not_and] at hA
      exact lt_of_not_ge (hA hu)
  have hprod : Integrable (fun u => w u * ell u) (volume.restrict (Ici q)) := by
    apply hdom.mono_nonneg (hw.mul hm).aestronglyMeasurable _ he
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact mul_nonneg (hw0 u hu) (h0 u)
  refine ⟨hprod, (integral_mono_ae hprod hdom he).trans ?_⟩
  rw [integral_add (hAi.const_mul B) (hi.const_mul M), integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hset : A ∩ Ici q = A := Set.inter_eq_left.mpr (fun u hu => hu.1)
  rw [hset]
  exact add_le_add (by rfl) (mul_le_mul_of_nonneg_left hmass hM)

/-- Elliptic covariance domination transfers the reference leverage estimate
to a frame orthonormal for the actual covariance. The original history Gram
may be singular and its conditioning does not enter the bound. -/
theorem rpow_historyLeverage_covariance_bound {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (z : κ → ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) {s α c : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α < 0) (hc : 0 < c)
    (hstop : ∀ i, s ≤ σ i) (C : (ι → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ v, c * ‖historyTimeVector Finset.univ v σ target center
      (fun i _ => hages i) 0‖ ^ 2 ≤ ‖C v‖ ^ 2)
    (horth : Orthonormal ℂ (fun k => C (z k))) :
    Fintype.card κ ≤ Fintype.card ι ∧
    (∫ u in Ici 0, historyLeverage z σ target center u) ≤ (Fintype.card κ : ℝ) / c ∧
    Integrable (fun u => u ^ α * historyLeverage z σ target center u)
      (volume.restrict (Ici 0)) ∧
    (∫ u in Ici 0, u ^ α * historyLeverage z σ target center u) ≤
      ((Fintype.card κ : ℝ) / c) * (s / 2) ^ α * (1 + 2 / (α + 1)) := by
  let R : ℝ := (Fintype.card κ : ℝ) / c
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have henergy : (∑ k, ‖historyTimeVector Finset.univ (z k) σ target center
      (fun i _ => hages i) 0‖ ^ 2) ≤ R := by
    calc
      _ ≤ ∑ _k : κ, (1 / c : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        have h := hcov (z k)
        rw [horth.norm_eq_one k, one_pow] at h
        apply (le_div_iff₀ hc).mpr
        nlinarith
      _ = R := by simp [R, div_eq_mul_inv]
  have hmass : (∫ u in Ici 0, historyLeverage z σ target center u) ≤ R := by
    rw [integral_historyLeverage_energy z σ target center hages 0]
    exact henergy
  have hearly : ∀ u ∈ Icc (0 : ℝ) (0 + s / 2),
      historyLeverage z σ target center u ≤ (4 / s) * R := by
    intro u hu
    exact (historyLeverage_early_energy_bound z σ target center hages hs
      (fun i => by simpa using hstop i) hu).trans
      (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hs2 : 0 < s / 2 := by positivity
  have hi : IntegrableOn (fun u : ℝ => u ^ α) (Icc 0 (s / 2)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegral.intervalIntegrable_rpow' hα (a := 0) (b := s / 2)).1
  have he := weighted_density_bound (historyLeverage z σ target center) (fun u : ℝ => u ^ α)
    hs hR (Real.rpow_nonneg hs2.le α) (historyLeverage_measurable z σ target center hages)
    (historyLeverage_integrable z σ target center hages 0)
    (historyLeverage_nonneg z σ target center) hmass hearly (measurable_id.pow_const α)
    (fun u hu => Real.rpow_nonneg hu α) (by simpa only [zero_add] using hi)
    (fun u hu => Real.rpow_le_rpow_of_nonpos hs2 (by linarith) hα0.le)
  have hn : α + 1 ≠ 0 := by linarith
  have hint : (∫ u in Icc (0 : ℝ) (s / 2), u ^ α) =
      (s / 2) ^ (α + 1) / (α + 1) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs2.le,
      integral_rpow (Or.inl hα), Real.zero_rpow hn, sub_zero]
  have hrank : Fintype.card κ ≤ Fintype.card ι := by
    have hl := LinearIndependent.of_comp C horth.linearIndependent
    simpa using hl.fintype_card_le_finrank
  refine ⟨hrank, hmass, he.1, he.2.trans_eq ?_⟩
  simp only [zero_add, hint]
  rw [Real.rpow_add hs2, Real.rpow_one]
  dsimp only [R]
  field_simp
  ring

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Genuine Haar translation of a circle L² function. -/
def circleTranslate (y : HeatCircle) (f : CircleL2) : CircleL2 :=
  Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right AddCircle.haarAddCircle y) f

theorem circleTranslate_norm (y : HeatCircle) (f : CircleL2) : ‖circleTranslate y f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (measurePreserving_sub_right AddCircle.haarAddCircle y)

theorem circleTranslate_coe (y : HeatCircle) (f : CircleL2) :
    (circleTranslate y f : HeatCircle → ℂ) =ᵐ[AddCircle.haarAddCircle] fun x => f (x - y) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right AddCircle.haarAddCircle y)

theorem continuous_circleTranslate : Continuous (fun p : HeatCircle × CircleL2 => circleTranslate p.1 p.2) := by
  let g : C(HeatCircle × CircleL2, C(HeatCircle, HeatCircle)) :=
    (ContinuousMap.mk (fun p : HeatCircle × HeatCircle => p.2 - p.1) (by fun_prop)).curry.comp
      ContinuousMap.fst
  exact continuous_snd.compMeasurePreservingLp g.continuous
    (fun p => measurePreserving_sub_right AddCircle.haarAddCircle p.1) (by norm_num)

/-- A positive convolution of one signed physical L² input, with its genuine
circle translates. No pointwise spatial supremum of the input is used. -/
theorem circle_convolution_average_bound (μ : Measure ℝ) [SFinite μ]
    (k : ℝ × HeatCircle → ℝ) (hk : Measurable k) (hk0 : ∀ p, 0 ≤ k p)
    (w : ℝ → ℝ) (f : ℝ → CircleL2) (hf : AEStronglyMeasurable f μ)
    {K : ℝ} (_hK : 0 ≤ K) (hfw : ∀ᵐ u ∂μ, ‖f u‖ ≤ K * w u)
    (hkw : Integrable (fun p => w p.1 * k p) (μ.prod AddCircle.haarAddCircle)) :
    Integrable (fun p : ℝ × HeatCircle => k p • circleTranslate p.2 (f p.1))
      (μ.prod AddCircle.haarAddCircle) ∧
    ‖∫ p : ℝ × HeatCircle, k p • circleTranslate p.2 (f p.1)
      ∂μ.prod AddCircle.haarAddCircle‖ ≤
      K * (∫ p : ℝ × HeatCircle, w p.1 * k p ∂μ.prod AddCircle.haarAddCircle) := by
  have htrans : AEStronglyMeasurable (fun p : ℝ × HeatCircle => circleTranslate p.2 (f p.1))
      (μ.prod AddCircle.haarAddCircle) :=
    continuous_circleTranslate.comp_aestronglyMeasurable
      (measurable_snd.aestronglyMeasurable.prodMk hf.comp_fst)
  have hmeas := hk.aestronglyMeasurable.smul htrans
  have hpoint : ∀ᵐ p : ℝ × HeatCircle ∂μ.prod AddCircle.haarAddCircle,
      ‖k p • circleTranslate p.2 (f p.1)‖ ≤ K * (w p.1 * k p) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfw] with p hp
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hk0 p), circleTranslate_norm]
    have he := mul_le_mul_of_nonneg_left hp (hk0 p)
    nlinarith
  have hi := (hkw.const_mul K).mono' hmeas hpoint
  refine ⟨hi, (norm_integral_le_integral_norm _).trans ?_⟩
  exact (integral_mono_ae hi.norm (hkw.const_mul K) hpoint).trans_eq (integral_const_mul K _)

/-- Actual Fubini identifies a positive kernel's weighted space/time mass
with the weighted integral of its spatial marginal. -/
theorem weighted_kernel_mass (μ : Measure ℝ) [SFinite μ]
    (k : ℝ × HeatCircle → ℝ) (hk : Measurable k) (hk0 : ∀ p, 0 ≤ k p)
    (hki : ∀ u, Integrable (fun y => k (u, y)) AddCircle.haarAddCircle)
    (w : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ᵐ u ∂μ, 0 ≤ w u)
    (m : ℝ → ℝ) (hm : ∀ u, (∫ y, k (u, y) ∂AddCircle.haarAddCircle) = m u)
    (hwm : Integrable (fun u => w u * m u) μ) :
    Integrable (fun p => w p.1 * k p) (μ.prod AddCircle.haarAddCircle) ∧
    (∫ p : ℝ × HeatCircle, w p.1 * k p ∂μ.prod AddCircle.haarAddCircle) =
      ∫ u, w u * m u ∂μ := by
  have hi : Integrable (fun p : ℝ × HeatCircle => w p.1 * k p)
      (μ.prod AddCircle.haarAddCircle) := by
    apply (integrable_prod_iff ((hw.comp measurable_fst).mul hk).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun u => (hki u).const_mul (w u)), hwm.congr ?_⟩
    filter_upwards [hw0] with u hu
    rw [← hm u, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by
      change w u * k (u, y) = ‖w u * k (u, y)‖
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu (hk0 (u, y)))])
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by
    change (∫ y, w u * k (u, y) ∂AddCircle.haarAddCircle) = w u * m u
    rw [integral_const_mul, hm u])

/-- The one signed L² input estimate for any translated physical history
leverage kernel. Its required spatial marginal is the actual full-history
trace, whose weighted bound was proved above. -/
theorem historyLeverage_convolution_bound (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) {s α : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α < 0) (hstop : ∀ i, s ≤ σ i)
    (horth : Orthonormal ℂ (fun k => historyTimeVector Finset.univ (z k)
      σ target center (fun i _ => hages i) 0))
    (k : ℝ × HeatCircle → ℝ) (hk : Measurable k) (hk0 : ∀ p, 0 ≤ k p)
    (hki : ∀ u, Integrable (fun y => k (u, y)) AddCircle.haarAddCircle)
    (hkm : ∀ u, (∫ y, k (u, y) ∂AddCircle.haarAddCircle) = historyLeverage z σ target center u)
    (f : ℝ → CircleL2) (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    {K : ℝ} (hK : 0 ≤ K)
    (hfw : ∀ᵐ u ∂volume.restrict (Ici 0), ‖f u‖ ≤ K * u ^ α) :
    Integrable (fun p : ℝ × HeatCircle => k p • circleTranslate p.2 (f p.1))
      ((volume.restrict (Ici 0)).prod AddCircle.haarAddCircle) ∧
    ‖∫ p : ℝ × HeatCircle, k p • circleTranslate p.2 (f p.1)
      ∂(volume.restrict (Ici 0)).prod AddCircle.haarAddCircle‖ ≤
      K * ((Fintype.card κ : ℝ) * (s / 2) ^ α * (1 + 2 / (α + 1))) := by
  have hpow := rpow_historyLeverage_bound z σ target center hages hs hα hα0 hstop horth
  have hw0 : ∀ᵐ u ∂volume.restrict (Ici (0 : ℝ)), 0 ≤ u ^ α := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact Real.rpow_nonneg hu α
  obtain ⟨hi, hm⟩ := weighted_kernel_mass (volume.restrict (Ici 0)) k hk hk0 hki
    (fun u => u ^ α) (measurable_id.pow_const α) hw0
    (historyLeverage z σ target center) hkm hpow.1
  obtain ⟨hconv, hbound⟩ := circle_convolution_average_bound
    (volume.restrict (Ici 0)) k hk hk0 (fun u => u ^ α) f hf hK hfw hi
  rw [hm] at hbound
  exact ⟨hconv, hbound.trans (mul_le_mul_of_nonneg_left hpow.2 hK)⟩

/-- An explicit jointly measurable physical Fourier representative of the heat
kernel. This is used to build the actual positive spatial leverage density. -/
def physicalCircleHeat (t : ℝ) (x y : HeatCircle) : ℂ :=
  ∑' n : ℤ, heatCoeff t x n * fourier n y

theorem measurable_physicalCircleHeat (x : HeatCircle) :
    Measurable (fun p : ℝ × HeatCircle => physicalCircleHeat p.1 x p.2) := by
  apply Measurable.tsum
  intro n
  have hc : Measurable (fun p : ℝ × HeatCircle => heatCoeff p.1 x n) := by
    unfold heatCoeff
    fun_prop
  exact hc.mul ((map_continuous (fourier n)).measurable.comp measurable_snd)

theorem physicalCircleHeat_ae {t : ℝ} (ht : 0 < t) (x : HeatCircle) :
    physicalCircleHeat t x =ᵐ[AddCircle.haarAddCircle] (circleHeat t x : HeatCircle → ℂ) := by
  let b := fourierBasis (T := 2 * Real.pi)
  let f : ℤ → CircleL2 := fun n => heatCoeff t x n • b n
  have hn : Summable (fun n : ℤ => ‖heatCoeff t x n‖) := by
    have hs := HeatTrace.multiplier_int_summable (Λ := 1) (ρ := 0) (t := t)
      (by norm_num) le_rfl ht
    convert hs using 1
    funext n
    have hphase : ‖fourier (-n) x‖ = 1 := Circle.norm_coe _
    simp only [HeatTrace.multiplier, neg_zero, Real.rpow_zero, one_mul, heatCoeff,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hphase, one_mul]
  have hnf : Summable (fun n => ‖f n‖) := by
    simpa only [f, norm_smul, b.orthonormal.norm_eq_one, mul_one] using hn
  have hsum : HasSum f (circleHeat t x) := by
    simpa only [f, b, fourierBasis_repr, circleHeat_fourierCoeff ht] using
      b.hasSum_repr (circleHeat t x)
  have hae := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnf)
  rw [hsum.tsum_eq] at hae
  have hterms : ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle, ∀ n : ℤ,
      f n y = heatCoeff t x n * fourier n y := by
    apply ae_all_iff.mpr
    intro n
    have hsmul := Lp.coeFn_smul (heatCoeff t x n) (b n)
    have hb : (b n : HeatCircle → ℂ) =ᵐ[AddCircle.haarAddCircle] fourier n := by
      simpa only [b, coe_fourierBasis] using coeFn_fourierLp 2 n
    filter_upwards [hsmul, hb] with y hy hby
    change (heatCoeff t x n • b n : CircleL2) y = _
    rw [hy, Pi.smul_apply, smul_eq_mul, hby]
  filter_upwards [hae, hterms] with y hy hty
  exact (hy.congr_fun (fun n => (hty n).symm)).tsum_eq

def physicalHistory (z : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (p : ℝ × HeatCircle) : ℂ :=
  ∑ i, if p.1 < σ i then z i * physicalCircleHeat (target i - p.1) (center i) p.2 else 0

theorem measurable_physicalHistory (z : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle) :
    Measurable (physicalHistory z σ target center) := by
  apply Finset.measurable_fun_sum
  intro i _
  apply Measurable.ite (measurableSet_lt measurable_fst measurable_const)
  · exact measurable_const.mul ((measurable_physicalCircleHeat (center i)).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd))
  · exact measurable_const

theorem physicalHistory_ae (z : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (u : ℝ) :
    (fun y => physicalHistory z σ target center (u, y)) =ᵐ[AddCircle.haarAddCircle]
      (historyF Finset.univ z σ target center u : HeatCircle → ℂ) := by
  let terms : ι → CircleL2 := fun i => if u < σ i then z i • circleHeat (target i - u) (center i) else 0
  have hterm : ∀ i, (fun y => if u < σ i then
      z i * physicalCircleHeat (target i - u) (center i) y else 0) =ᵐ[AddCircle.haarAddCircle]
      (terms i : HeatCircle → ℂ) := by
    intro i
    by_cases hu : u < σ i
    · have hh := physicalCircleHeat_ae (by linarith [hages i] : 0 < target i - u) (center i)
      have hs := Lp.coeFn_smul (z i) (circleHeat (target i - u) (center i))
      filter_upwards [hh, hs] with y hy hsy
      simp only [terms, ite_eq_left hu]
      rw [hsy, Pi.smul_apply, smul_eq_mul, hy]
    · simp only [terms, ite_eq_right hu]
      convert! (Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle).symm using 1
  have hterms := ae_all_iff.mpr hterm
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ terms
  filter_upwards [hterms, hsum] with y hy hsy
  change (∑ i, if u < σ i then z i * physicalCircleHeat (target i - u) (center i) y else 0) =
    (∑ i, terms i) y
  rw [hsy]
  exact Finset.sum_congr rfl (fun i _ => hy i)

def physicalLeverage (z : κ → ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (p : ℝ × HeatCircle) : ℝ := ∑ k, ‖physicalHistory (z k) σ target center p‖ ^ 2

theorem physicalLeverage_properties (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i, σ i ≤ target i) :
    Measurable (physicalLeverage z σ target center) ∧
    (∀ p, 0 ≤ physicalLeverage z σ target center p) ∧
    (∀ u, Integrable (fun y => physicalLeverage z σ target center (u, y)) AddCircle.haarAddCircle) ∧
    (∀ u, (∫ y, physicalLeverage z σ target center (u, y) ∂AddCircle.haarAddCircle) =
      historyLeverage z σ target center u) := by
  have hki : ∀ k u, Integrable (fun y => ‖physicalHistory (z k) σ target center (u, y)‖ ^ 2)
      AddCircle.haarAddCircle := by
    intro k u
    have h := Lp.memLp (historyF Finset.univ (z k) σ target center u)
    have hi := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
    exact hi.congr ((physicalHistory_ae (z k) σ target center hages u).symm.fun_comp
      (fun x : ℂ => ‖x‖ ^ 2))
  refine ⟨?_, fun p => Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_, ?_⟩
  · apply Finset.measurable_fun_sum
    intro k _
    exact (measurable_physicalHistory (z k) σ target center).norm.pow_const 2
  · intro u
    exact integrable_finsetSum Finset.univ (fun k _ => hki k u)
  · intro u
    change (∫ y, ∑ k, ‖physicalHistory (z k) σ target center (u, y)‖ ^ 2
      ∂AddCircle.haarAddCircle) = _
    rw [integral_finsetSum Finset.univ (fun k _ => hki k u)]
    apply Finset.sum_congr rfl
    intro k _
    rw [L2_norm_sq_eq_integral]
    exact integral_congr_ae ((physicalHistory_ae (z k) σ target center hages u).fun_comp
      (fun x : ℂ => ‖x‖ ^ 2))

/-- The actual positive spatial leverage kernel of a finite physical heat
history frame acts on one signed L² input with the manuscript's weighted
time gain. The kernel, its marginal, translations, and Bochner integral are
all concrete; no spatial transfer estimate is assumed. -/
theorem physicalLeverage_convolution_covariance_bound {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (z : κ → ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) {s α c : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α < 0) (hc : 0 < c)
    (hstop : ∀ i, s ≤ σ i) (C : (ι → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ v, c * ‖historyTimeVector Finset.univ v σ target center
      (fun i _ => hages i) 0‖ ^ 2 ≤ ‖C v‖ ^ 2)
    (horth : Orthonormal ℂ (fun k => C (z k)))
    (f : ℝ → CircleL2) (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    {K : ℝ} (hK : 0 ≤ K)
    (hfw : ∀ᵐ u ∂volume.restrict (Ici 0), ‖f u‖ ≤ K * u ^ α) :
    Integrable (fun p : ℝ × HeatCircle => physicalLeverage z σ target center p •
      circleTranslate p.2 (f p.1)) ((volume.restrict (Ici 0)).prod AddCircle.haarAddCircle) ∧
    ‖∫ p : ℝ × HeatCircle, physicalLeverage z σ target center p • circleTranslate p.2 (f p.1)
      ∂(volume.restrict (Ici 0)).prod AddCircle.haarAddCircle‖ ≤
      K * (((Fintype.card κ : ℝ) / c) * (s / 2) ^ α * (1 + 2 / (α + 1))) := by
  obtain ⟨hm, h0, hi, hmarginal⟩ := physicalLeverage_properties z σ target center hages
  obtain ⟨_, _, hweight, hbound⟩ := rpow_historyLeverage_covariance_bound
    z σ target center hages hs hα hα0 hc hstop C hcov horth
  have hw0 : ∀ᵐ u ∂volume.restrict (Ici (0 : ℝ)), 0 ≤ u ^ α := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact Real.rpow_nonneg hu α
  obtain ⟨hprod, hmass⟩ := weighted_kernel_mass (volume.restrict (Ici 0))
    (physicalLeverage z σ target center) hm h0 hi (fun u => u ^ α)
    (measurable_id.pow_const α) hw0 (historyLeverage z σ target center) hmarginal hweight
  obtain ⟨hconv, hconvbound⟩ := circle_convolution_average_bound (volume.restrict (Ici 0))
    (physicalLeverage z σ target center) hm h0 (fun u => u ^ α) f hf hK hfw hprod
  rw [hmass] at hconvbound
  exact ⟨hconv, hconvbound.trans (mul_le_mul_of_nonneg_left hbound hK)⟩

/-- The physical kernel translates with its original observation center. -/
theorem physicalCircleHeat_translate (t : ℝ) (x y a : HeatCircle) :
    physicalCircleHeat t (x + a) (y + a) = physicalCircleHeat t x y := by
  have harg : ∀ (n : ℤ) (b d : HeatCircle), fourier n (b + d) = fourier n b * fourier n d := by
    intro n b d
    simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  unfold physicalCircleHeat
  apply tsum_congr
  intro n
  have hcancel : fourier (-n) a * fourier n a = 1 := by
    rw [← fourier_add, neg_add_cancel, fourier_zero]
  unfold heatCoeff
  rw [harg, harg]
  calc
    _ = (fourier (-n) x * (Real.exp (-t * (n : ℝ) ^ 2) : ℂ) * fourier n y) *
        (fourier (-n) a * fourier n a) := by ring
    _ = _ := by rw [hcancel, mul_one]

theorem physicalHistory_translate (z : ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (u : ℝ) (y a : HeatCircle) :
    physicalHistory z σ target (fun i => center i + a) (u, y + a) =
      physicalHistory z σ target center (u, y) := by
  unfold physicalHistory
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [physicalCircleHeat_translate]
  · rfl

theorem physicalLeverage_translate (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (u : ℝ) (y a : HeatCircle) :
    physicalLeverage z σ target (fun i => center i + a) (u, y + a) =
      physicalLeverage z σ target center (u, y) := by
  unfold physicalLeverage
  simp_rw [physicalHistory_translate]

/-- A full orthonormal actual covariance-range frame can always be lifted to
observation coefficients. Thus the frame hypotheses above are realizable at
every rank, including rank zero and singular covariance configurations. -/
theorem exists_covariance_range_frame {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (C : (ι → ℂ) →ₗ[ℂ] G) :
    ∃ z : Fin (Module.finrank ℂ C.range) → ι → ℂ,
      Orthonormal ℂ (fun k => C (z k)) ∧
      (∀ k, C (z k) = ((stdOrthonormalBasis ℂ C.range) k : G)) := by
  classical
  let b := stdOrthonormalBasis ℂ C.range
  let z : Fin (Module.finrank ℂ C.range) → ι → ℂ := fun k => Classical.choose (b k).property
  have hz : ∀ k, C (z k) = (b k : G) := fun k => Classical.choose_spec (b k).property
  refine ⟨z, ?_, hz⟩
  refine ⟨?_, ?_⟩
  · intro k
    change ‖C (z k)‖ = 1
    rw [hz]
    exact b.orthonormal.norm_eq_one k
  · intro k l hkl
    change inner ℂ (C (z k)) (C (z l)) = 0
    rw [hz, hz]
    exact b.orthonormal.inner_eq_zero hkl

end FiniteHistoryLeverage

end SHE.GaussianAudit
