module

public import SHE.WeightedScoreExpansion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section

namespace SHE.WeightedWordMarking
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct
open scoped BigOperators NNReal Matrix.Norms.L2Operator
variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι] {n : ℕ}

/-- The literal three marks after the unchanged old-score average:
full centered covariance mark, full centered mean mark, and each
omitted-leaf full-profile baseline derivative. -/
def mark (s : Finset ι) (μ : Measure X) (w : X → ℝ) (shift : X → State n)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (R : State n → ℝ) (a : ι → State n → ℝ)
    (b db : ι → ℝ → ℝ) (covMark : (State n → ℝ) → ℝ → State n → ℝ)
    (base D : State n) (θ : ℝ) : ℝ :=
  covMark (WeightedBorelAverage.average μ w shift (test s R a (fun i => b i θ))) θ (base+θ • D)+
    ProfileReserve.affineMeanMark A
      (WeightedBorelAverage.average μ w shift (test s R a (fun i => b i θ))) base D θ-
    ∑ i ∈ s,db i θ*gaussianAverage (A θ)
      (WeightedBorelAverage.average μ w shift (test (s.erase i) R a (fun j => b j θ))) (base+θ • D)

theorem ae_hasDerivAt (s : Finset ι) (μ : Measure X) [SFinite μ]
    (w : X → ℝ) (hw : Integrable w μ) (hwmeas : Measurable w)
    (shift : X → State n) (hs : Measurable shift)
    {A : ℝ → Matrix (Fin n) (Fin n) ℝ} (Q : ProfileReserve A)
    {K : ℝ≥0} (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
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
    ∀ᵐ θ ∂volume, HasDerivAt (WeightedGaussianWord.word s μ w shift A R a b base D)
      (mark s μ w shift A R a b db covMark base D θ) θ := by
  have hder := WeightedGaussianWord.ae_hasDerivAt s μ w hw hwmeas shift hs Q hK R a b db
    hR ha B M hB hM hRb hab hb base D hD covMark hcov
  have hm (t : Finset ι) (ht : t ∈ s.powerset) :=
    measurable_monomial t R a hR (fun i hi => ha i (Finset.mem_powerset.mp ht hi))
  have hmono (t : Finset ι) (ht : t ∈ s.powerset) :=
    WeightedBorelAverage.measurable μ w hwmeas shift hs _ (hm t ht)
  have hmb (t : Finset ι) (ht : t ∈ s.powerset) (z : State n) :=
    WeightedBorelAverage.bound μ w hw shift hs _ (hm t ht) (B*∏ i ∈ t,M i)
      (mul_nonneg hB (Finset.prod_nonneg (fun i hi => hM i (Finset.mem_powerset.mp ht hi))))
      (monomial_bound t R a B M hB (fun i hi => hM i (Finset.mem_powerset.mp ht hi)) hRb
        (fun i hi => hab i (Finset.mem_powerset.mp ht hi))) z
  filter_upwards [hder,hcov,(Filter.eventually_all_finset s).mpr hb] with θ hθ hcθ hbθ
  have hc (t : Finset ι) (ht : t ∈ s.powerset) := hcθ _ (hmono t ht) _ (hmb t ht) (base+θ • D)
  have hsum := HasDerivAt.fun_sum (u:=s.powerset) (fun t ht =>
    (hc t ht).const_mul (coefficient s t (fun i => b i θ)))
  have heq : (fun η => ∑ t ∈ s.powerset,coefficient s t (fun i => b i θ)*
      gaussianAverage (A η) (WeightedBorelAverage.average μ w shift (monomial R a t)) (base+θ • D))=
      fun η => gaussianAverage (A η)
        (WeightedBorelAverage.average μ w shift (test s R a (fun i => b i θ))) (base+θ • D) := by
    funext η
    exact (WeightedGaussianWord.expansion s μ w hw hwmeas shift hs (A η) R a _
      hR ha B M hB hM hRb hab _).symm
  rw [heq] at hsum
  have htest := measurable_test s R a (fun i => b i θ) hR ha
  have hfull := hcθ _ (WeightedBorelAverage.measurable μ w hwmeas shift hs _ htest) _
    (fun z => WeightedBorelAverage.bound μ w hw shift hs _ htest (B*∏ i ∈ s,(M i+|b i θ|))
      (mul_nonneg hB (Finset.prod_nonneg (fun i hi => add_nonneg (hM i hi) (abs_nonneg _))))
      (test_bound s R a _ B M hB hM hRb hab) z) (base+θ • D)
  have hcovsum := hsum.unique hfull
  have hbaseline := WeightedCenteredExpansion.baseline_expansion s μ w hw hwmeas shift hs
    (A θ) R a b (fun i => db i θ) θ hbθ hR ha B M hB hM hRb hab (base+θ • D)
  have hmean := WeightedCenteredExpansion.integral_score_expansion s μ w hw hwmeas shift hs
    (A θ) R a (fun i => b i θ) hR ha B M hB hM hRb hab (base+θ • D)
    (MeasurableGaussianScores.firstScore (A θ) D) (FiniteWordScores.firstScore_integrable (A θ) D)
  have hemark : mark s μ w shift A R a b db covMark base D θ=
      WeightedGaussianWord.mark s μ w shift A R a b db covMark base D θ := by
    simp only [mark,WeightedGaussianWord.mark,ProfileReserve.affineMeanMark,mul_add,Finset.sum_add_distrib]
    rw [hbaseline,hcovsum,←hmean]
    ring
  rw [hemark]
  exact hθ

end SHE.WeightedWordMarking
