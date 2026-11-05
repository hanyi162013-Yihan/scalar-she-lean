module

public import SHEStochastic.BrownianGaussianStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertGaussianFinite
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

theorem vector_step (P : FiniteScalarIto.Family F μ H ι) {n : ℕ} (a : Fin n → ι)
    (ha : Function.Injective a) (v : Fin n → C)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) {R : Ω → C} (hR : Measurable[F s] R) :
    μ[fun ω ↦ Complex.exp (((∑ i : Fin n, inner ℝ (v i) (R ω) *
      (P.W (a i) t ω - P.W (a i) s ω) : ℝ) : ℂ) * Complex.I) | F s] =ᵐ[μ]
    (fun ω ↦ (Real.exp (-(((t - s : ℝ≥0) : ℝ) *
      ∑ i : Fin n, (inner ℝ (v i) (R ω)) ^ 2) / 2) : ℂ)) := by
  let r : Ω → WordRecursion.State n := fun ω ↦ WithLp.toLp 2 (fun i ↦ inner ℝ (v i) (R ω))
  have hr : Measurable[F s] r := by
    letI : MeasurableSpace Ω := F s
    exact (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.mpr
      fun i ↦ (innerSL ℝ (v i)).measurable.comp hR)
  have hh := FiniteScalarIto.condExp_gaussian_step_injective P a ha s t hst htH hr
  simpa only [r, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, star_trivial,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat] using hh

/-- Every finite coordinate projection of a frozen Hilbert row has the
conditional Gaussian law with its actual projected squared norm. -/
theorem finset_step (P : FiniteScalarIto.Family F μ H ι) (v : ι → C) (S : Finset ι)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) {R : Ω → C} (hR : Measurable[F s] R) :
    μ[fun ω ↦ Complex.exp (((∑ i ∈ S, inner ℝ (v i) (R ω) *
      (P.W i t ω - P.W i s ω) : ℝ) : ℂ) * Complex.I) | F s] =ᵐ[μ]
    (fun ω ↦ (Real.exp (-(((t - s : ℝ≥0) : ℝ) *
      ∑ i ∈ S, (inner ℝ (v i) (R ω)) ^ 2) / 2) : ℂ)) := by
  classical
  let a : Fin (Fintype.card S) → ι := fun i ↦ ((Fintype.equivFin S).symm i).val
  have ha : Function.Injective a := Subtype.coe_injective.comp (Fintype.equivFin S).symm.injective
  have hs (f : ι → ℝ) : (∑ i : Fin (Fintype.card S), f (a i)) = ∑ i ∈ S, f i :=
    ((Fintype.equivFin S).symm.sum_comp (fun i : S ↦ f i)).trans (Finset.sum_coe_sort S f)
  have h1 (ω : Ω) : (∑ i : Fin (Fintype.card S), inner ℝ (v (a i)) (R ω) *
      (P.W (a i) t ω - P.W (a i) s ω)) =
      ∑ i ∈ S, inner ℝ (v i) (R ω) * (P.W i t ω - P.W i s ω) :=
    hs (fun i ↦ inner ℝ (v i) (R ω) * (P.W i t ω - P.W i s ω))
  have h2 (ω : Ω) : (∑ i : Fin (Fintype.card S), (inner ℝ (v (a i)) (R ω)) ^ 2) =
      ∑ i ∈ S, (inner ℝ (v i) (R ω)) ^ 2 := hs (fun i ↦ (inner ℝ (v i) (R ω)) ^ 2)
  simpa only [h1, h2] using vector_step P a ha (fun i ↦ v (a i)) s t hst htH hR

end SHEStochastic.HilbertGaussianFinite
