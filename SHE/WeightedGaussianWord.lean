module

public import SHE.WeightedBorelAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.WeightedGaussianWord
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct
open scoped BigOperators NNReal Matrix.Norms.L2Operator
variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι] {n : ℕ}

def word (s : Finset ι) (μ : Measure X) (w : X → ℝ) (shift : X → State n)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (R : State n → ℝ) (a : ι → State n → ℝ)
    (b : ι → ℝ → ℝ) (base D : State n) (θ : ℝ) : ℝ :=
  gaussianAverage (A θ)
    (WeightedBorelAverage.average μ w shift (test s R a (fun i => b i θ))) (base + θ • D)

/-- Each baseline is differentiated in the finite polynomial expansion.
The old weight and all rough leaves are unchanged. -/
def mark (s : Finset ι) (μ : Measure X) (w : X → ℝ) (shift : X → State n)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (R : State n → ℝ) (a : ι → State n → ℝ)
    (b db : ι → ℝ → ℝ)
    (covMark : (State n → ℝ) → ℝ → State n → ℝ) (base D : State n) (θ : ℝ) : ℝ :=
  ∑ t ∈ s.powerset, (
    coefficientDerivative s t (fun i => b i θ) (fun i => db i θ) *
      gaussianAverage (A θ) (WeightedBorelAverage.average μ w shift (monomial R a t)) (base + θ • D) +
    coefficient s t (fun i => b i θ) *
      (covMark (WeightedBorelAverage.average μ w shift (monomial R a t)) θ (base + θ • D) +
        ProfileReserve.affineMeanMark A (WeightedBorelAverage.average μ w shift (monomial R a t)) base D θ))

theorem expansion (s : Finset ι) (μ : Measure X) [SFinite μ]
    (w : X → ℝ) (hw : Integrable w μ) (hwmeas : Measurable w)
    (shift : X → State n) (hs : Measurable shift)
    (A : Matrix (Fin n) (Fin n) ℝ) (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) (z : State n) :
    gaussianAverage A (WeightedBorelAverage.average μ w shift (test s R a b)) z =
      ∑ t ∈ s.powerset, coefficient s t b *
        gaussianAverage A (WeightedBorelAverage.average μ w shift (monomial R a t)) z := by
  unfold gaussianAverage
  simp_rw [WeightedBorelAverage.test_expansion s μ w hw shift hs R a b hR ha B M hB hM hRb hab]
  rw [integral_finsetSum s.powerset]
  · simp_rw [integral_const_mul]
  · intro t ht
    have hts := Finset.mem_powerset.mp ht
    have hm := measurable_monomial t R a hR (fun i hi => ha i (hts hi))
    exact (integrable_bounded _ _
      ((WeightedBorelAverage.measurable μ w hwmeas shift hs _ hm).comp
        (measurable_const.add measurable_id))
      ((B * ∏ i ∈ t, M i) * ∫ x, |w x| ∂μ)
      (fun y => WeightedBorelAverage.bound μ w hw shift hs _ hm (B * ∏ i ∈ t, M i)
        (mul_nonneg hB (Finset.prod_nonneg (fun i hi => hM i (hts hi))))
        (monomial_bound t R a B M hB (fun i hi => hM i (hts hi)) hRb
          (fun i hi => hab i (hts hi))) (z + y))).const_mul _

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
    ∀ᵐ θ ∂volume, HasDerivAt (word s μ w shift A R a b base D)
      (mark s μ w shift A R a b db covMark base D θ) θ := by
  have hm (t : Finset ι) (ht : t ∈ s.powerset) :=
    measurable_monomial t R a hR (fun i hi => ha i (Finset.mem_powerset.mp ht hi))
  have hbound (t : Finset ι) (ht : t ∈ s.powerset) (z : State n) :=
    WeightedBorelAverage.bound μ w hw shift hs _ (hm t ht) (B * ∏ i ∈ t, M i)
      (mul_nonneg hB (Finset.prod_nonneg (fun i hi => hM i (Finset.mem_powerset.mp ht hi))))
      (monomial_bound t R a B M hB (fun i hi => hM i (Finset.mem_powerset.mp ht hi)) hRb
        (fun i hi => hab i (Finset.mem_powerset.mp ht hi))) z
  have hc (t : Finset ι) (ht : t ∈ s.powerset) : ∀ᵐ θ ∂volume, ∀ z,
      HasDerivAt (fun η => gaussianAverage (A η)
        (WeightedBorelAverage.average μ w shift (monomial R a t)) z)
        (covMark (WeightedBorelAverage.average μ w shift (monomial R a t)) θ z) θ := by
    filter_upwards [hcov] with θ hθ
    exact hθ _ (WeightedBorelAverage.measurable μ w hwmeas shift hs _ (hm t ht)) _ (hbound t ht)
  have hd (t : Finset ι) (ht : t ∈ s.powerset) := Q.ae_hasDerivAt_affine_total hK
    (WeightedBorelAverage.average μ w shift (monomial R a t))
    (WeightedBorelAverage.measurable μ w hwmeas shift hs _ (hm t ht)) _ (hbound t ht)
    base D hD (covMark _) (hc t ht)
  filter_upwards [(Filter.eventually_all_finset s).mpr hb,
    (Filter.eventually_all_finset s.powerset).mpr hd] with θ hbθ hdθ
  have hh := HasDerivAt.fun_sum (u := s.powerset) (fun t ht =>
    (coefficient_hasDerivAt s t b (fun i => db i θ) θ hbθ).mul (hdθ t ht))
  have he : (fun η => ∑ t ∈ s.powerset, coefficient s t (fun i => b i η) *
      gaussianAverage (A η) (WeightedBorelAverage.average μ w shift (monomial R a t)) (base + η • D)) =
      word s μ w shift A R a b base D := by
    funext η
    exact (expansion s μ w hw hwmeas shift hs (A η) R a _ hR ha B M hB hM hRb hab _).symm
  simpa only [he, mark, Pi.mul_apply] using hh

theorem exists_lipschitz (s : Finset ι) (μ : Measure X) [SFinite μ]
    (w : X → ℝ) (hw : Integrable w μ) (hwmeas : Measurable w)
    (shift : X → State n) (hs : Measurable shift)
    {A : ℝ → Matrix (Fin n) (Fin n) ℝ} (Q : ProfileReserve A)
    {K : ℝ≥0} (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M N : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hN : ∀ i ∈ s, 0 ≤ N i) (hRb : ∀ z, |R z| ≤ B)
    (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i)
    (L : ι → ℝ≥0) (hlip : ∀ i ∈ s, LipschitzWith (L i) (b i))
    (hb : ∀ i ∈ s, ∀ θ, |b i θ| ≤ N i)
    (base D : State n) (hD : D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range) :
    ∃ J : ℝ≥0, LipschitzWith J (word s μ w shift A R a b base D) := by
  have hW : 0 ≤ ∫ x, |w x| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  have hterm (t : Finset ι) (ht : t ∈ s.powerset) : ∃ J : ℝ≥0,
      LipschitzWith J (fun θ => coefficient s t (fun i => b i θ) *
        gaussianAverage (A θ) (WeightedBorelAverage.average μ w shift (monomial R a t)) (base + θ • D)) := by
    have hts := Finset.mem_powerset.mp ht
    have hm := measurable_monomial t R a hR (fun i hi => ha i (hts hi))
    let F := WeightedBorelAverage.average μ w shift (monomial R a t)
    let T := (B * ∏ i ∈ t, M i) * ∫ x, |w x| ∂μ
    have hT : 0 ≤ T := mul_nonneg (mul_nonneg hB (Finset.prod_nonneg (fun i hi => hM i (hts hi)))) hW
    have hFb (z : State n) : |F z| ≤ T :=
      WeightedBorelAverage.bound μ w hw shift hs _ hm _
        (mul_nonneg hB (Finset.prod_nonneg (fun i hi => hM i (hts hi))))
        (monomial_bound t R a B M hB (fun i hi => hM i (hts hi)) hRb
          (fun i hi => hab i (hts hi))) z
    obtain ⟨J, hJ⟩ := FiniteGaussianWord.exists_lipschitz_prod (s \ t) (fun i θ => -b i θ) L N
      (fun i hi => hN i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => (hlip i (Finset.mem_sdiff.mp hi).1).neg)
      (fun i hi θ => by simpa only [abs_neg] using hb i (Finset.mem_sdiff.mp hi).1 θ)
    obtain ⟨V, hV⟩ := Q.exists_lipschitz_affine hK F
      (WeightedBorelAverage.measurable μ w hwmeas shift hs _ hm) T hFb base D hD
    exact FiniteGaussianWord.exists_lipschitz_bounded_mul hJ hV (∏ i ∈ s \ t, N i) T
      (Finset.prod_nonneg (fun i hi => hN i (Finset.mem_sdiff.mp hi).1)) hT
      (fun θ => by
        change |∏ i ∈ s \ t, -b i θ| ≤ _
        simp only [Finset.abs_prod, abs_neg]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun i hi => hb i (Finset.mem_sdiff.mp hi).1 θ))
      (fun θ => average_bound (A θ) F T hFb _)
  classical
  let J : Finset ι → ℝ≥0 := fun t => if ht : t ∈ s.powerset then (hterm t ht).choose else 0
  have hJ (t : Finset ι) (ht : t ∈ s.powerset) : LipschitzWith (J t)
      (fun θ => coefficient s t (fun i => b i θ) *
        gaussianAverage (A θ) (WeightedBorelAverage.average μ w shift (monomial R a t)) (base + θ • D)) := by
    simpa only [J, dite_eq_left ht] using (hterm t ht).choose_spec
  have hh : LipschitzWith (∑ t ∈ s.powerset, J t)
      (fun θ => ∑ t ∈ s.powerset, coefficient s t (fun i => b i θ) *
        gaussianAverage (A θ) (WeightedBorelAverage.average μ w shift (monomial R a t)) (base + θ • D)) := by
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    rw [Real.dist_eq, ← Finset.sum_sub_distrib, NNReal.coe_sum, Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun t ht => (hJ t ht).dist_le_mul θ η))
  refine ⟨∑ t ∈ s.powerset, J t, ?_⟩
  convert hh using 1
  funext θ
  exact expansion s μ w hw hwmeas shift hs (A θ) R a _ hR ha B M hB hM hRb hab _

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
        word s μ w shift A R a b base D t - word s μ w shift A R a b base D r := by
  obtain ⟨J, hJ⟩ := exists_lipschitz s μ w hw hwmeas shift hs Q hK R a b hR ha B M N hB hM hN
    hRb hab L hlip hbnd base D hD
  exact LipschitzIntegralIdentity.integral_eq_sub hJ
    (ae_hasDerivAt s μ w hw hwmeas shift hs Q hK R a b db hR ha B M hB hM hRb hab
      hb base D hD covMark hcov) r t

end SHE.WeightedGaussianWord
