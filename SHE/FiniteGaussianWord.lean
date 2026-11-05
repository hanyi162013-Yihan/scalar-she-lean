module

public import SHE.FiniteCenteredProduct

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FiniteGaussianWord
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct
open scoped BigOperators NNReal Matrix.Norms.L2Operator
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

theorem exists_lipschitz_bounded_mul {f g : ℝ → ℝ} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ θ, |f θ| ≤ B) (hc : ∀ θ, |g θ| ≤ C) :
    ∃ J : ℝ≥0, LipschitzWith J (fun θ => f θ * g θ) := by
  let J : ℝ := B * L + C * K
  have hJ : 0 ≤ J := add_nonneg (mul_nonneg hB L.coe_nonneg) (mul_nonneg hC K.coe_nonneg)
  refine ⟨⟨J, hJ⟩, LipschitzWith.of_dist_le_mul (fun θ η => ?_)⟩
  change |f θ * g θ - f η * g η| ≤ J * |θ - η|
  calc
    _ = |f θ * (g θ - g η) + (f θ - f η) * g η| := by congr 1; ring
    _ ≤ |f θ| * |g θ - g η| + |f θ - f η| * |g η| := by
      simpa only [abs_mul] using abs_add_le (f θ * (g θ - g η)) ((f θ - f η) * g η)
    _ ≤ B * ((L : ℝ) * |θ - η|) + ((K : ℝ) * |θ - η|) * C :=
      add_le_add (mul_le_mul (hb θ) (hg.dist_le_mul θ η) (abs_nonneg _) hB)
        (mul_le_mul (hf.dist_le_mul θ η) (hc η) (abs_nonneg _) (mul_nonneg K.coe_nonneg (abs_nonneg _)))
    _ = J * |θ - η| := by dsimp [J]; ring

theorem exists_lipschitz_prod (s : Finset ι) (b : ι → ℝ → ℝ)
    (L : ι → ℝ≥0) (B : ι → ℝ) (hB : ∀ i ∈ s, 0 ≤ B i)
    (hlip : ∀ i ∈ s, LipschitzWith (L i) (b i))
    (hb : ∀ i ∈ s, ∀ θ, |b i θ| ≤ B i) :
    ∃ J : ℝ≥0, LipschitzWith J (fun θ => ∏ i ∈ s, b i θ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using (LipschitzWith.const (1 : ℝ))⟩
  | @insert i s hi ih =>
    obtain ⟨J, hJ⟩ := ih (fun k hk => hB k (Finset.mem_insert_of_mem hk))
      (fun k hk => hlip k (Finset.mem_insert_of_mem hk))
      (fun k hk => hb k (Finset.mem_insert_of_mem hk))
    obtain ⟨T, hT⟩ := exists_lipschitz_bounded_mul (hlip i (Finset.mem_insert_self _ _)) hJ
      (B i) (∏ k ∈ s, B k) (hB i (Finset.mem_insert_self _ _))
      (Finset.prod_nonneg (fun k hk => hB k (Finset.mem_insert_of_mem hk)))
      (hb i (Finset.mem_insert_self _ _)) (fun θ => by
        rw [Finset.abs_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun k hk => hb k (Finset.mem_insert_of_mem hk) θ))
    exact ⟨T, by simpa only [Finset.prod_insert hi] using hT⟩

def word (s : Finset ι) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ → ℝ)
    (base D : State n) (θ : ℝ) : ℝ :=
  gaussianAverage (A θ) (test s R a (fun i => b i θ)) (base + θ • D)

/-- Full mean and covariance score marking of the fixed monomial expansion.
The marks use the same covariance and the same physical direction for every
subset; no old score or rough test is differentiated. -/
def scoreMark (s : Finset ι) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ → ℝ)
    (covMark : (State n → ℝ) → ℝ → State n → ℝ) (base D : State n) (θ : ℝ) : ℝ :=
  ∑ t ∈ s.powerset, coefficient s t (fun i => b i θ) *
    (covMark (monomial R a t) θ (base + θ • D) +
      ProfileReserve.affineMeanMark A (monomial R a t) base D θ)

def baselineMark (s : Finset ι) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R : State n → ℝ) (a : ι → State n → ℝ) (b db : ι → ℝ → ℝ)
    (base D : State n) (θ : ℝ) : ℝ :=
  ∑ i ∈ s, db i θ * gaussianAverage (A θ)
    (test (s.erase i) R a (fun j => b j θ)) (base + θ • D)

theorem ae_hasDerivAt_word (s : Finset ι) {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (Q : ProfileReserve A) {K : ℝ≥0} (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (R : State n → ℝ) (a : ι → State n → ℝ) (b db : ι → ℝ → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i)
    (hb : ∀ i ∈ s, ∀ᵐ θ ∂volume, HasDerivAt (b i) (db i θ) θ)
    (base D : State n) (hD : D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range)
    (covMark : (State n → ℝ) → ℝ → State n → ℝ)
    (hcov : ∀ t ∈ s.powerset, ∀ᵐ θ ∂volume, ∀ z,
      HasDerivAt (fun η => gaussianAverage (A η) (monomial R a t) z)
        (covMark (monomial R a t) θ z) θ) :
    ∀ᵐ θ ∂volume, HasDerivAt (word s A R a b base D)
      (scoreMark s A R a b covMark base D θ - baselineMark s A R a b db base D θ) θ := by
  have hm (t : Finset ι) (ht : t ∈ s.powerset) := Q.ae_hasDerivAt_affine_total hK
    (monomial R a t) (measurable_monomial t R a hR (fun i hi => ha i (Finset.mem_powerset.mp ht hi)))
    (B * ∏ i ∈ t, M i)
    (fun z => monomial_bound t R a B M hB (fun i hi => hM i (Finset.mem_powerset.mp ht hi))
      hRb (fun i hi => hab i (Finset.mem_powerset.mp ht hi)) z)
    base D hD (covMark (monomial R a t)) (hcov t ht)
  filter_upwards [(Filter.eventually_all_finset s).mpr hb,
    (Filter.eventually_all_finset s.powerset).mpr hm] with θ hbθ hmθ
  have hsum := HasDerivAt.fun_sum (u := s.powerset) (fun t ht =>
    (coefficient_hasDerivAt s t b (fun i => db i θ) θ hbθ).mul (hmθ t ht))
  have he : (fun η => ∑ t ∈ s.powerset, coefficient s t (fun i => b i η) *
      gaussianAverage (A η) (monomial R a t) (base + η • D)) = word s A R a b base D := by
    funext η
    exact (average_expansion s (A η) R a _ hR ha B M hB hM hRb hab _).symm
  simp only [Pi.mul_apply] at hsum
  rw [he] at hsum
  convert hsum using 1
  simp only [scoreMark, baselineMark, Finset.sum_add_distrib]
  rw [average_derivative_expansion s (A θ) R a b (fun i => db i θ) θ hbθ hR ha B M hB hM hRb hab]
  ring

theorem exists_lipschitz_word (s : Finset ι) {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (Q : ProfileReserve A) {K : ℝ≥0} (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M N : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hN : ∀ i ∈ s, 0 ≤ N i) (hRb : ∀ z, |R z| ≤ B)
    (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i)
    (L : ι → ℝ≥0) (hlip : ∀ i ∈ s, LipschitzWith (L i) (b i))
    (hb : ∀ i ∈ s, ∀ θ, |b i θ| ≤ N i)
    (base D : State n) (hD : D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range) :
    ∃ J : ℝ≥0, LipschitzWith J (word s A R a b base D) := by
  have hterm (t : Finset ι) (ht : t ∈ s.powerset) : ∃ J : ℝ≥0,
      LipschitzWith J (fun θ => coefficient s t (fun i => b i θ) *
        gaussianAverage (A θ) (monomial R a t) (base + θ • D)) := by
    have hts := Finset.mem_powerset.mp ht
    obtain ⟨J, hJ⟩ := exists_lipschitz_prod (s \ t) (fun i θ => -b i θ) L N
      (fun i hi => hN i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => (hlip i (Finset.mem_sdiff.mp hi).1).neg)
      (fun i hi θ => by simpa only [abs_neg] using hb i (Finset.mem_sdiff.mp hi).1 θ)
    obtain ⟨T, hT⟩ := Q.exists_lipschitz_affine hK (monomial R a t)
      (measurable_monomial t R a hR (fun i hi => ha i (hts hi))) (B * ∏ i ∈ t, M i)
      (fun z => monomial_bound t R a B M hB (fun i hi => hM i (hts hi)) hRb
        (fun i hi => hab i (hts hi)) z) base D hD
    exact exists_lipschitz_bounded_mul hJ hT (∏ i ∈ s \ t, N i) (B * ∏ i ∈ t, M i)
      (Finset.prod_nonneg (fun i hi => hN i (Finset.mem_sdiff.mp hi).1))
      (mul_nonneg hB (Finset.prod_nonneg (fun i hi => hM i (hts hi))))
      (fun θ => by
        change |∏ i ∈ s \ t, -b i θ| ≤ _
        simp only [Finset.abs_prod, abs_neg]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun i hi => hb i (Finset.mem_sdiff.mp hi).1 θ))
      (fun θ => average_bound (A θ) _ _
        (fun z => monomial_bound t R a B M hB (fun i hi => hM i (hts hi)) hRb
          (fun i hi => hab i (hts hi)) z) _)
  classical
  let J : Finset ι → ℝ≥0 := fun t => if ht : t ∈ s.powerset then (hterm t ht).choose else 0
  have hJ (t : Finset ι) (ht : t ∈ s.powerset) : LipschitzWith (J t)
      (fun θ => coefficient s t (fun i => b i θ) *
        gaussianAverage (A θ) (monomial R a t) (base + θ • D)) := by
    simpa only [J, dif_pos ht] using (hterm t ht).choose_spec
  refine ⟨∑ t ∈ s.powerset, J t, ?_⟩
  have hh : LipschitzWith (∑ t ∈ s.powerset, J t)
      (fun θ => ∑ t ∈ s.powerset, coefficient s t (fun i => b i θ) *
        gaussianAverage (A θ) (monomial R a t) (base + θ • D)) := by
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    rw [Real.dist_eq, ← Finset.sum_sub_distrib, NNReal.coe_sum, Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun t ht => (hJ t ht).dist_le_mul θ η))
  have he : (fun θ => ∑ t ∈ s.powerset, coefficient s t (fun i => b i θ) *
      gaussianAverage (A θ) (monomial R a t) (base + θ • D)) = word s A R a b base D := by
    funext θ
    exact (average_expansion s (A θ) R a _ hR ha B M hB hM hRb hab _).symm
  simpa only [he] using hh

theorem integral_word (s : Finset ι) {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
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
    (hcov : ∀ t ∈ s.powerset, ∀ᵐ θ ∂volume, ∀ z,
      HasDerivAt (fun η => gaussianAverage (A η) (monomial R a t) z)
        (covMark (monomial R a t) θ z) θ) (r t : ℝ) :
    let mark := fun θ => scoreMark s A R a b covMark base D θ - baselineMark s A R a b db base D θ
    IntervalIntegrable mark volume r t ∧
      (∫ θ in r..t, mark θ) = word s A R a b base D t - word s A R a b base D r := by
  obtain ⟨J, hJ⟩ := exists_lipschitz_word s Q hK R a b hR ha B M N hB hM hN hRb hab L hlip hbnd base D hD
  exact LipschitzIntegralIdentity.integral_eq_sub hJ
    (ae_hasDerivAt_word s Q hK R a b db hR ha B M hB hM hRb hab hb base D hD covMark hcov) r t

end SHE.FiniteGaussianWord
