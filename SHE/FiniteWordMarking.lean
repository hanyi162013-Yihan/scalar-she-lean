module

public import SHE.ControlledFixedReserve

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FiniteWordMarking
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct
open scoped BigOperators NNReal Matrix.Norms.L2Operator
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

def mark (s : Finset ι) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R : State n → ℝ) (a : ι → State n → ℝ) (b db : ι → ℝ → ℝ)
    (covMark : (State n → ℝ) → ℝ → State n → ℝ) (base D : State n) (θ : ℝ) : ℝ :=
  covMark (test s R a (fun i => b i θ)) θ (base + θ • D) +
    (∫ y, test s R a (fun i => b i θ) (base + θ • D + y) *
      MeasurableGaussianScores.firstScore (A θ) D y ∂multivariateGaussian 0 (A θ)) -
    FiniteGaussianWord.baselineMark s A R a b db base D θ

/-- A common covariance-marking event for all bounded Borel tests gives
the genuine finite-product rule. The covariance mark is applied directly
to the entire centered product, rather than to an unbounded family of
parameter-dependent score matrices. -/
theorem ae_hasDerivAt (s : Finset ι) {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (Q : ProfileReserve A) {K : ℝ≥0} (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (R : State n → ℝ) (a : ι → State n → ℝ) (b db : ι → ℝ → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i)
    (hb : ∀ i ∈ s, ∀ᵐ θ ∂volume, HasDerivAt (b i) (db i θ) θ)
    (base D : State n) (hD : D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range)
    (covMark : (State n → ℝ) → ℝ → State n → ℝ)
    (hcov : ∀ᵐ θ ∂volume, ∀ (F : State n → ℝ), Measurable F →
      ∀ N : ℝ, (∀ z, |F z| ≤ N) → ∀ z,
        HasDerivAt (fun η => gaussianAverage (A η) F z) (covMark F θ z) θ) :
    ∀ᵐ θ ∂volume, HasDerivAt (FiniteGaussianWord.word s A R a b base D)
      (mark s A R a b db covMark base D θ) θ := by
  have hmono (t : Finset ι) (ht : t ∈ s.powerset) : ∀ᵐ θ ∂volume, ∀ z,
      HasDerivAt (fun η => gaussianAverage (A η) (monomial R a t) z)
        (covMark (monomial R a t) θ z) θ := by
    filter_upwards [hcov] with θ hθ
    exact hθ _ (measurable_monomial t R a hR (fun i hi => ha i (Finset.mem_powerset.mp ht hi)))
      (B * ∏ i ∈ t, M i)
      (fun z => monomial_bound t R a B M hB (fun i hi => hM i (Finset.mem_powerset.mp ht hi))
        hRb (fun i hi => hab i (Finset.mem_powerset.mp ht hi)) z)
  have hder := FiniteGaussianWord.ae_hasDerivAt_word s Q hK R a b db hR ha B M hB hM
    hRb hab hb base D hD covMark hmono
  filter_upwards [hder, hcov] with θ hθ hcθ
  have hc (t : Finset ι) (ht : t ∈ s.powerset) := hcθ (monomial R a t)
    (measurable_monomial t R a hR (fun i hi => ha i (Finset.mem_powerset.mp ht hi)))
    (B * ∏ i ∈ t, M i)
    (fun z => monomial_bound t R a B M hB (fun i hi => hM i (Finset.mem_powerset.mp ht hi))
      hRb (fun i hi => hab i (Finset.mem_powerset.mp ht hi)) z) (base + θ • D)
  have hsum := HasDerivAt.fun_sum (u := s.powerset) (fun t ht =>
    (hc t ht).const_mul (coefficient s t (fun i => b i θ)))
  have heq : (fun η => ∑ t ∈ s.powerset, coefficient s t (fun i => b i θ) *
      gaussianAverage (A η) (monomial R a t) (base + θ • D)) =
      fun η => gaussianAverage (A η) (test s R a (fun i => b i θ)) (base + θ • D) := by
    funext η
    exact (average_expansion s (A η) R a _ hR ha B M hB hM hRb hab _).symm
  rw [heq] at hsum
  have hfull := hcθ (test s R a (fun i => b i θ)) (measurable_test s R a _ hR ha)
    (B * ∏ i ∈ s, (M i + |b i θ|))
    (test_bound s R a _ B M hB hM hRb hab) (base + θ • D)
  have hcovsum := hsum.unique hfull
  convert hθ using 1
  simp only [mark, FiniteGaussianWord.scoreMark, ProfileReserve.affineMeanMark,
    mul_add, Finset.sum_add_distrib]
  rw [hcovsum, ← FiniteWordScores.meanMark_expansion s (A θ) R a _ hR ha B M hB hM hRb hab]

theorem integral (s : Finset ι) {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (Q : ProfileReserve A) {K : ℝ≥0} (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (R : State n → ℝ) (a : ι → State n → ℝ) (b db : ι → ℝ → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M N : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hN : ∀ i ∈ s, 0 ≤ N i) (hRb : ∀ z, |R z| ≤ B)
    (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i)
    (L : ι → ℝ≥0) (hlip : ∀ i ∈ s, LipschitzWith (L i) (b i))
    (hbnd : ∀ i ∈ s, ∀ θ, |b i θ| ≤ N i)
    (hb : ∀ i ∈ s, ∀ᵐ θ ∂volume, HasDerivAt (b i) (db i θ) θ)
    (base D : State n) (hD : D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range)
    (covMark : (State n → ℝ) → ℝ → State n → ℝ)
    (hcov : ∀ᵐ θ ∂volume, ∀ (F : State n → ℝ), Measurable F →
      ∀ N : ℝ, (∀ z, |F z| ≤ N) → ∀ z,
        HasDerivAt (fun η => gaussianAverage (A η) F z) (covMark F θ z) θ) (r t : ℝ) :
    IntervalIntegrable (mark s A R a b db covMark base D) volume r t ∧
      (∫ θ in r..t, mark s A R a b db covMark base D θ) =
        FiniteGaussianWord.word s A R a b base D t - FiniteGaussianWord.word s A R a b base D r := by
  obtain ⟨J, hJ⟩ := FiniteGaussianWord.exists_lipschitz_word s Q hK R a b hR ha B M N hB hM hN
    hRb hab L hlip hbnd base D hD
  exact LipschitzIntegralIdentity.integral_eq_sub hJ
    (ae_hasDerivAt s Q hK R a b db hR ha B M hB hM hRb hab hb base D hD covMark hcov) r t

end SHE.FiniteWordMarking
