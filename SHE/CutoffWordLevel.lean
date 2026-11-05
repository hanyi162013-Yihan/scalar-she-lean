module

public import SHE.CutoffInsertionCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Automatic extension of genuine physical word histories on a separated
time cutoff. Coefficients and reference profiles are TOTAL variances.
Every original target and stop is retained in the growing observation list. -/
noncomputable section
namespace SHE.CutoffWordLevel
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion CovarianceMatrix CovarianceEndpoint GaussianContinuity GaussianConvolution
open GaussianItoTest SmoothWords SmoothCylinders UniformSmooth UniformInsertions
open VariableObservations MeasurableWords CutoffInsertionCore
open scoped Matrix.Norms.Elementwise
open Classical

abbrev State (n : ℕ) := WordRecursion.State n

structure ReferenceData where
  totalVariance : ℝ → ℝ
  totalVariance_smooth : BoundedSmooth totalVariance
  reference : ℝ × HeatCircle → ℝ
  reference_measurable : Measurable reference
  upper : ℝ
  upper_nonneg : 0 ≤ upper
  reference_bound : ∀ p, |reference p| ≤ upper
  reference_nonneg : ∀ p, 0 ≤ reference p
  base : ℝ
  horizon : ℝ
  base_nonneg : 0 ≤ base
  ordered : base ≤ horizon

variable {P : Type*} [MeasurableSpace P]

def reindexFamily {Q : Type*} [MeasurableSpace Q] {n : ℕ} (Z : Family P n)
    (f : Q → P) (hf : Measurable f) : Family Q n where
  observations := fun p => Z.observations (f p)
  stop_measurable := fun i => (Z.stop_measurable i).comp hf
  target_measurable := fun i => (Z.target_measurable i).comp hf
  center_measurable := fun i => (Z.center_measurable i).comp hf

theorem uniform_reindex {Q : Type*} {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : P → E → G} (hF : UniformBoundedSmooth F) (f : Q → P) :
    UniformBoundedSmooth (fun p => F (f p)) := by
  refine ⟨fun p => hF.smooth (f p), fun k => ?_⟩
  obtain ⟨M, hMn, hM⟩ := hF.bounds k
  exact ⟨M, hMn, fun p z => hM (f p) z⟩

structure Level (R : ReferenceData) (P : Type*) [MeasurableSpace P] (n : ℕ) where
  observations : Family P n
  terminal : P → ℝ
  terminal_measurable : Measurable terminal
  terminal_base : ∀ p, R.base ≤ terminal p
  terminal_horizon : ∀ p, terminal p ≤ R.horizon
  targets_after : ∀ p i, terminal p ≤ (observations.observations p i).target
  stops_after : ∀ p i, terminal p ≤ (observations.observations p i).stop
  test : P → State n → ℝ
  test_uniform : UniformBoundedSmooth test
  test_measurable : Measurable (fun p : P × State n => test p.1 p.2)

namespace Level
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)

def window (p : P) : EndpointWindow n where
  coefficient := R.reference
  measurable := R.reference_measurable
  observations := L.observations.observations p
  left := R.base
  right := L.terminal p
  upper := R.upper
  ordered := L.terminal_base p
  upper_nonneg := R.upper_nonneg
  target_after := L.targets_after p
  bounded := fun t _ x => R.reference_bound (t, x)
  nonneg := fun t _ x => R.reference_nonneg (t, x)

def nodeTime (p : P × (ℝ × HeatCircle)) : ℝ := ClippedCovariance.clip R.base (L.terminal p.1) p.2.1

theorem nodeTime_measurable : Measurable L.nodeTime :=
  measurable_const.max ((L.terminal_measurable.comp measurable_fst).min measurable_snd.fst)

theorem nodeTime_mem (p : P × (ℝ × HeatCircle)) : L.nodeTime p ∈ Icc R.base (L.terminal p.1) :=
  ClippedCovariance.clip_mem (L.terminal_base p.1) p.2.1

def Good (δ : ℝ) (p : P × (ℝ × HeatCircle)) : Prop := R.base < p.2.1 ∧ p.2.1 ≤ L.terminal p.1 - δ

theorem good_measurableSet (δ : ℝ) : MeasurableSet {p | L.Good δ p} :=
  (measurableSet_lt measurable_const measurable_snd.fst).inter
    (measurableSet_le measurable_snd.fst ((L.terminal_measurable.comp measurable_fst).sub_const δ))

theorem good_time {δ : ℝ} (hδ : 0 < δ) {p : P × (ℝ × HeatCircle)} (hp : L.Good δ p) :
    p.2.1 ∈ Ioo R.base (L.terminal p.1) := ⟨hp.1, by linarith [hp.2]⟩

theorem nodeTime_eq {δ : ℝ} (hδ : 0 < δ) {p : P × (ℝ × HeatCircle)} (hp : L.Good δ p) :
    L.nodeTime p = p.2.1 := ClippedCovariance.clip_eq (Ioo_subset_Icc_self (L.good_time hδ hp))

def nodeCovariance (p : P × (ℝ × HeatCircle)) : PositiveCovariance n :=
  ⟨covariance R.reference (L.observations.observations p.1) (L.nodeTime p) (L.terminal p.1),
    covariance_posSemidef_endpoint R.reference R.reference_measurable (L.observations.observations p.1)
      R.upper_nonneg (L.nodeTime_mem p).2 (L.targets_after p.1)
      (fun t _ x => R.reference_bound (t, x)) (fun t _ x => R.reference_nonneg (t, x))⟩

theorem nodeCovariance_measurable : Measurable L.nodeCovariance := by
  let Z : Family (P × (ℝ × HeatCircle)) n := reindexFamily L.observations Prod.fst measurable_fst
  exact Z.positive_covariance_measurable (R.reference_measurable.comp measurable_snd)
    L.nodeTime_measurable (L.terminal_measurable.comp measurable_fst) (fun p => (L.nodeTime_mem p).2)
    (fun p => (L.nodeCovariance p).property)

def averagedTest (p : P × (ℝ × HeatCircle)) : State n → ℝ :=
  gaussianAverage (L.nodeCovariance p).val (L.test p.1)

theorem averagedTest_uniform : UniformBoundedSmooth L.averagedTest :=
  (uniform_reindex L.test_uniform Prod.fst).average
    (fun p => multivariateGaussian (0 : State n) (L.nodeCovariance p).val) (fun _ => inferInstance)

theorem averagedTest_measurable :
    Measurable (fun p : (P × (ℝ × HeatCircle)) × State n => L.averagedTest p.1 p.2) := by
  have hF : Measurable (fun p : (P × (ℝ × HeatCircle)) × State n => L.test p.1.1 p.2) :=
    L.test_measurable.comp (measurable_fst.fst.prodMk measurable_snd)
  exact gaussian_average_measurable L.nodeCovariance_measurable hF (fun p => (L.test_uniform.smooth p.1).continuous)

def cutoffRow (δ : ℝ) (p : P × (ℝ × HeatCircle)) : State n := by
  classical
  exact if L.Good δ p then heatRow (L.observations.observations p.1) (L.nodeTime p) p.2.2 else 0

theorem cutoffRow_measurable (δ : ℝ) : Measurable (L.cutoffRow δ) := by
  classical
  have hr := L.observations.heatRow_measurable.comp
    (measurable_fst.prodMk (L.nodeTime_measurable.prodMk measurable_snd.snd))
  exact hr.ite (L.good_measurableSet δ) measurable_const

theorem cutoffRow_bound {δ : ℝ} (hδ : 0 < δ) (p : P × (ℝ × HeatCircle)) :
    ‖L.cutoffRow δ p‖ ≤ Real.sqrt n * heatRowBound δ := by
  classical
  by_cases hp : L.Good δ p
  · simp only [cutoffRow, hp, ite_true]
    apply heatRow_norm_bound _ hδ
    intro i
    rw [L.nodeTime_eq hδ hp]
    linarith [L.targets_after p.1 i, hp.2]
  · simp only [cutoffRow, hp, ite_false, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (heatRowBound_pos hδ).le

def childTest (δ : ℝ) (p : P × (ℝ × HeatCircle)) : State (n + 1) → ℝ :=
  core R.totalVariance (R.reference (L.nodeTime p, p.2.2)) (L.cutoffRow δ p) (L.averagedTest p)

theorem childTest_uniform {δ : ℝ} (hδ : 0 < δ) : UniformBoundedSmooth (L.childTest δ) :=
  core_uniform R.totalVariance_smooth L.averagedTest_uniform _ _ R.upper_nonneg
    (fun p => R.reference_bound _) (mul_nonneg (Real.sqrt_nonneg _) (heatRowBound_pos hδ).le) (L.cutoffRow_bound hδ)

theorem childTest_measurable (δ : ℝ) :
    Measurable (fun p : (P × (ℝ × HeatCircle)) × State (n + 1) => L.childTest δ p.1 p.2) :=
  core_measurable R.totalVariance_smooth.smooth.continuous.measurable
    (R.reference_measurable.comp (L.nodeTime_measurable.prodMk measurable_snd.snd))
    (L.cutoffRow_measurable δ) L.averagedTest_measurable
    (fun p => (L.averagedTest_uniform.smooth p).of_le (by simp))

def childObservations : Family (P × (ℝ × HeatCircle)) (n + 1) :=
  reindexFamily L.observations.append
    (fun p => (p.1, (L.nodeTime p, p.2.2)))
    (measurable_fst.prodMk (L.nodeTime_measurable.prodMk measurable_snd.snd))

def extend (δ : ℝ) (hδ : 0 < δ) : Level R (P × (ℝ × HeatCircle)) (n + 1) where
  observations := L.childObservations
  terminal := L.nodeTime
  terminal_measurable := L.nodeTime_measurable
  terminal_base := fun p => (L.nodeTime_mem p).1
  terminal_horizon := fun p => (L.nodeTime_mem p).2.trans (L.terminal_horizon p.1)
  targets_after := by
    intro p i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_rfl
    · exact (L.nodeTime_mem p).2.trans (L.targets_after p.1 j)
  stops_after := by
    intro p i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_rfl
    · exact (L.nodeTime_mem p).2.trans (L.stops_after p.1 j)
  test := L.childTest δ
  test_uniform := L.childTest_uniform hδ
  test_measurable := L.childTest_measurable δ

/-- On the cutoff domain the next test is exactly the printed physical
Gaussian-average/covariance insertion. Outside it the zero extension
is explicit, so the full product history measure remains finite. -/
theorem childTest_eq {δ : ℝ} (hδ : 0 < δ) (p : P × (ℝ × HeatCircle)) :
    L.childTest δ p = if L.Good δ p then
      insertion R.totalVariance R.reference (L.observations.observations p.1) p.2.1 p.2.2
        (gaussianSemigroup R.reference (L.observations.observations p.1) p.2.1 (L.terminal p.1) (L.test p.1)) else 0 := by
  classical
  by_cases hp : L.Good δ p
  · simp only [hp, ite_true, childTest, cutoffRow]
    unfold averagedTest nodeCovariance
    change core _ _ _ (gaussianAverage (covariance R.reference (L.observations.observations p.1)
      (L.nodeTime p) (L.terminal p.1)) (L.test p.1)) = _
    rw [L.nodeTime_eq hδ hp]
    rfl
  · simp only [hp, ite_false, childTest, cutoffRow, core_zero]

end Level
end SHE.CutoffWordLevel
