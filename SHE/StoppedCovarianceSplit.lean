module

public import SHE.StoppedGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Exact positive Gaussian splitting for the literal individually stopped
history covariance. Old fractions can remain fixed while a residual
coefficient profile varies; all original physical observations are kept. -/
namespace SHE.StoppedCovarianceSplit
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier
  StoppedGaussianFeatures GaussianIncrement
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
  (hages : ∀ i, σ i ≤ target i) (q : ℝ)
include hages

theorem stoppedRow_memLp (i : Fin n) :
    MemLp (fun r => stoppedRow σ target center r i) 2 (historyMeasure q) := by
  have hm := stoppedRow_entry_measurable σ target center i
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi := realHistory_square_product_integrable σ target center hages (basisCoeff i) q
  simpa only [realHistory_basisCoeff] using hi

/-- Signed bounded profiles have genuine integrable covariance entries. -/
theorem covariance_entry_integrable {c : Domain → ℝ} (hc : Measurable c)
    {M : ℝ} (hcb : ∀ r, |c r| ≤ M) (i j : Fin n) :
    Integrable (fun r => c r * stoppedRow σ target center r i * stoppedRow σ target center r j)
      (historyMeasure q) := by
  have h := ((stoppedRow_memLp σ target center hages q i).integrable_mul
    (stoppedRow_memLp σ target center hages q j)).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using hcb r))
  convert! h using 1
  funext r
  simp only [Pi.mul_apply]
  ring

theorem covariance_add {c d : Domain → ℝ} (hc : Measurable c) (hd : Measurable d)
    {M N : ℝ} (hcb : ∀ r, |c r| ≤ M) (hdb : ∀ r, |d r| ≤ N) :
    StoppedGaussianFeatures.stoppedCovariance σ target center (fun r => c r + d r) q =
      StoppedGaussianFeatures.stoppedCovariance σ target center c q +
        StoppedGaussianFeatures.stoppedCovariance σ target center d q := by
  ext i j
  simp only [StoppedGaussianFeatures.stoppedCovariance, Matrix.add_apply, add_mul]
  exact integral_add (covariance_entry_integrable σ target center hages q hc hcb i j)
    (covariance_entry_integrable σ target center hages q hd hdb i j)

theorem covariance_sub {c d : Domain → ℝ} (hc : Measurable c) (hd : Measurable d)
    {M N : ℝ} (hcb : ∀ r, |c r| ≤ M) (hdb : ∀ r, |d r| ≤ N) :
    StoppedGaussianFeatures.stoppedCovariance σ target center (fun r => c r - d r) q =
      StoppedGaussianFeatures.stoppedCovariance σ target center c q -
        StoppedGaussianFeatures.stoppedCovariance σ target center d q := by
  ext i j
  simp only [StoppedGaussianFeatures.stoppedCovariance, Matrix.sub_apply, sub_mul]
  exact integral_sub (covariance_entry_integrable σ target center hages q hc hcb i j)
    (covariance_entry_integrable σ target center hages q hd hdb i j)

omit hages in
theorem covariance_const_mul (c : Domain → ℝ) (b : ℝ) :
    StoppedGaussianFeatures.stoppedCovariance σ target center (fun r => b * c r) q =
      b • StoppedGaussianFeatures.stoppedCovariance σ target center c q := by
  ext i j
  simp only [StoppedGaussianFeatures.stoppedCovariance, Matrix.smul_apply, smul_eq_mul,
    mul_assoc, integral_const_mul]

theorem covariance_posSemidef {c : Domain → ℝ} (hc : Measurable c) {M : ℝ}
    (hcb : ∀ r, 0 ≤ c r ∧ c r ≤ M) :
    (StoppedGaussianFeatures.stoppedCovariance σ target center c q).PosSemidef := by
  rw [← weightedFeature_gram σ target center c hc M hcb hages q]
  exact Matrix.posSemidef_gram ℝ _

/-- Exact convolution of the actual full stopped Gaussian laws under a
positive coefficient split. This is not a formal covariance decomposition. -/
theorem gaussian_positive_split {c d : Domain → ℝ} (hc : Measurable c) (hd : Measurable d)
    {M N : ℝ} (hcb : ∀ r, 0 ≤ c r ∧ c r ≤ M) (hdb : ∀ r, 0 ≤ d r ∧ d r ≤ N) :
    multivariateGaussian (0 : State n) (StoppedGaussianFeatures.stoppedCovariance σ target center c q) ∗
      multivariateGaussian 0 (StoppedGaussianFeatures.stoppedCovariance σ target center d q) =
      multivariateGaussian 0
        (StoppedGaussianFeatures.stoppedCovariance σ target center (fun r => c r + d r) q) := by
  rw [gaussian_convolution (covariance_posSemidef σ target center hages q hc hcb)
    (covariance_posSemidef σ target center hages q hd hdb),
    covariance_add σ target center hages q hc hd
      (fun r => (abs_of_nonneg (hcb r).1).trans_le (hcb r).2)
      (fun r => (abs_of_nonneg (hdb r).1).trans_le (hdb r).2)]

omit hages q in
theorem reserved_profile_bounds {c c₀ : Domain → ℝ} {ell M ε : ℝ}
    (_hell : 0 < ell) (hε : 0 ≤ ε) (hεM : ε * M ≤ ell / 2)
    (hc : ∀ r, ell ≤ c r ∧ c r ≤ M) (hc₀ : ∀ r, 0 ≤ c₀ r ∧ c₀ r ≤ M) (r : Domain) :
    0 ≤ ε * c₀ r ∧ ε * c₀ r ≤ ε * M ∧
      ell / 2 ≤ c r - ε * c₀ r ∧ c r - ε * c₀ r ≤ M := by
  have hf0 := mul_nonneg hε (hc₀ r).1
  have hfM := mul_le_mul_of_nonneg_left (hc₀ r).2 hε
  exact ⟨hf0, hfM, by linarith [(hc r).1], by linarith [(hc r).2]⟩

/-- A fixed old profile fraction and a varying elliptic residual yield an
exact Gaussian split at every parameter, without time-zero regularity or
any covariance eigenvector selection. -/
theorem gaussian_fixed_fraction_split {c c₀ : Domain → ℝ}
    (hc : Measurable c) (hc₀ : Measurable c₀) {ell M ε : ℝ}
    (hell : 0 < ell) (hε : 0 ≤ ε) (hεM : ε * M ≤ ell / 2)
    (hcb : ∀ r, ell ≤ c r ∧ c r ≤ M) (hc₀b : ∀ r, 0 ≤ c₀ r ∧ c₀ r ≤ M) :
    multivariateGaussian (0 : State n)
        (StoppedGaussianFeatures.stoppedCovariance σ target center (fun r => ε * c₀ r) q) ∗
      multivariateGaussian 0
        (StoppedGaussianFeatures.stoppedCovariance σ target center (fun r => c r - ε * c₀ r) q) =
      multivariateGaussian 0 (StoppedGaussianFeatures.stoppedCovariance σ target center c q) := by
  have hb (r : Domain) := reserved_profile_bounds hell hε hεM hcb hc₀b r
  have hf : ∀ r, 0 ≤ ε * c₀ r ∧ ε * c₀ r ≤ ε * M := fun r => ⟨(hb r).1, (hb r).2.1⟩
  have hr : ∀ r, 0 ≤ c r - ε * c₀ r ∧ c r - ε * c₀ r ≤ M :=
    fun r => ⟨(by linarith [(hb r).2.2.1]), (hb r).2.2.2⟩
  have h := gaussian_positive_split σ target center hages q (hc₀.const_mul ε)
    (hc.sub (hc₀.const_mul ε)) hf hr
  have heq : (fun r => ε * c₀ r + (c - fun r => ε * c₀ r) r) = c := by
    funext r
    change ε * c₀ r + (c r - ε * c₀ r) = c r
    ring
  rw [heq] at h
  convert! h using 1

end SHE.StoppedCovarianceSplit
