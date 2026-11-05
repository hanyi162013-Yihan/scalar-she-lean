module

public import SHE.WeightedWordMarking

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.WeightedWordMarking
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct
open scoped BigOperators NNReal Matrix.Norms.L2Operator
variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι] {n : ℕ}

/-- The literal three marked terms integrate to the endpoint difference
of the entire old-weighted centered word. -/
theorem integral (s : Finset ι) (μ : Measure X) [SFinite μ]
    (w : X → ℝ) (hw : Integrable w μ) (hwmeas : Measurable w)
    (shift : X → State n) (hs : Measurable shift)
    {A : ℝ → Matrix (Fin n) (Fin n) ℝ} (Q : ProfileReserve A)
    {K : ℝ≥0} (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
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
    IntervalIntegrable (mark s μ w shift A R a b db covMark base D) volume r t ∧
      (∫ θ in r..t, mark s μ w shift A R a b db covMark base D θ) =
        WeightedGaussianWord.word s μ w shift A R a b base D t - WeightedGaussianWord.word s μ w shift A R a b base D r := by
  obtain ⟨J,hJ⟩ := WeightedGaussianWord.exists_lipschitz s μ w hw hwmeas shift hs Q hK R a b
    hR ha B M N hB hM hN hRb hab L hlip hbnd base D hD
  exact LipschitzIntegralIdentity.integral_eq_sub hJ
    (ae_hasDerivAt s μ w hw hwmeas shift hs Q hK R a b db hR ha B M hB hM hRb hab
      hb base D hD covMark hcov) r t

end SHE.WeightedWordMarking
