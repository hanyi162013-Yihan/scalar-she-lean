module

public import SHE.GaussianContinuity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.CovarianceContinuity
open MeasureTheory Set SHE.WordRecursion SHE.CovarianceMatrix SHE.GaussianContinuity
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem continuous_gaussian_average_comp {α E : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {n : ℕ}
    (C : α → Matrix (Fin n) (Fin n) ℝ) (hC : Continuous C) (hpos : ∀ x,(C x).PosSemidef)
    (m : α → State n) (hm : Continuous m) (F : State n → E) (hF : Continuous F)
    {K : ℝ} (hb : ∀ z,‖F z‖ ≤ K) :
    Continuous (fun x => ∫ y : State n,F (m x+y) ∂ProbabilityTheory.multivariateGaussian 0 (C x)) := by
  let P (x : α) : PositiveCovariance n := ⟨C x,hpos x⟩
  have hP : Continuous P := hC.subtype_mk hpos
  have havg := continuous_gaussian_average (n:=n) F hF hb
  have hh := havg.comp (hP.prodMk hm)
  exact hh

theorem covariance_continuousOn_left {n : ℕ} (c : ℝ × SHE.StoppedFourier.HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {δ M a b s : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hab : a ≤ b) (hgap : ∀ i,δ ≤ (Z i).target-b)
    (hbound : ∀ t ∈ Icc a b,∀ x,|c (t,x)| ≤ M) (hs : s ∈ Icc a b) :
    ContinuousOn (fun q => covariance c Z q s) (Icc a b) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hi := covariance_entry_intervalIntegrable c hc Z hδ hM hab hgap hbound i j
  have hh := (intervalIntegral.continuousOn_primitive_interval' hi (by simpa only [uIcc_of_le hab] using hs)).neg
  have he : (fun q => -(∫ t in s..q,covarianceDensity c Z t i j)) =
      fun q => covariance c Z q s i j := by
    funext q
    rw [intervalIntegral.integral_symm,neg_neg]
    rfl
  change ContinuousOn (fun q => -(∫ t in s..q,covarianceDensity c Z t i j)) (uIcc a b) at hh
  rw [he,uIcc_of_le hab] at hh
  exact hh

/-- The genuine backward Gaussian field is jointly continuous in its
current time and finite observation state throughout a positive-gap
window, with only measurable bounded nonnegative reference variance. -/
theorem continuous_gaussianSemigroup_window {n : ℕ}
    (c : ℝ × SHE.StoppedFourier.HeatCircle → ℝ) (hc : Measurable c) (Z : Fin n → Observation)
    {δ M a s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (has : a ≤ s)
    (hgap : ∀ i,δ ≤ (Z i).target-s) (hbound : ∀ t ∈ Icc a s,∀ x,|c (t,x)| ≤ M)
    (hnonneg : ∀ t ∈ Icc a s,∀ x,0 ≤ c (t,x))
    (F : State n → ℝ) (hF : Continuous F) {K : ℝ} (hK : ∀ z,|F z| ≤ K) :
    Continuous (fun p : {q : ℝ // q ∈ Icc a s} × State n =>
      gaussianSemigroup c Z p.1.val s F p.2) := by
  have hC : Continuous (fun p : {q : ℝ // q ∈ Icc a s} × State n => covariance c Z p.1.val s) :=
    ((continuousOn_iff_continuous_domRestrict).mp
      (covariance_continuousOn_left c hc Z hδ hM has hgap hbound ⟨has,le_rfl⟩)).comp continuous_fst
  have hpos (p : {q : ℝ // q ∈ Icc a s} × State n) : (covariance c Z p.1.val s).PosSemidef :=
    covariance_posSemidef c hc Z hδ hM p.1.property.2 hgap
      (fun t ht => hbound t ⟨p.1.property.1.trans ht.1,ht.2⟩)
      (fun t ht => hnonneg t ⟨p.1.property.1.trans ht.1,ht.2⟩)
  exact continuous_gaussian_average_comp _ hC hpos _ continuous_snd F hF
    (fun z => by simpa only [Real.norm_eq_abs] using hK z)

end SHE.CovarianceContinuity
