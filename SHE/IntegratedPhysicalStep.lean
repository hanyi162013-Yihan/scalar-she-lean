module

public import SHE.PhysicalRemainderMass
public import SHE.SmoothWords

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Integrating an actual physical Itô level over a finite cutoff-history
measure. The martingale version is identified with the genuine Itô term
on every history fiber, and its centering follows by actual Fubini. -/
noncomputable section
namespace SHE.IntegratedPhysicalStep
open Set MeasureTheory ProbabilityTheory Filter StoppedFourier
open WordRecursion CovarianceEndpoint GaussianItoTest PhysicalIto UniformSmooth
open PhysicalRemainderMass SmoothCylinders

abbrev State (n : ℕ) := WordRecursion.State n

structure LevelData (P Ω : Type*) (n : ℕ) where
  window : P → EndpointWindow n
  totalVariance : ℝ → ℝ
  state : P → Ω → ℝ → CircleL2
  field : P → Ω → ℝ × HeatCircle → ℝ
  test : P → State n → ℝ
  stochasticTerm : P → (ℝ → State n → ℝ) → Ω → ℝ

namespace LevelData
variable {P Ω : Type*} {n : ℕ} (D : LevelData P Ω n)

def leaf (p : P) (ω : Ω) : ℝ :=
  D.test p (observe (D.state p ω) (D.field p ω) (D.window p).observations (D.window p).right)

def reference (p : P) (ω : Ω) : ℝ :=
  backward (D.window p) (D.test p) (D.window p).left
    (observe (D.state p ω) (D.field p ω) (D.window p).observations (D.window p).left)

def remainder (p : P) (ω : Ω) : ℝ := wordRemainder (D.window p) D.totalVariance (D.state p ω) (D.field p ω) (D.test p)

def noiseVersion (p : P) (ω : Ω) : ℝ := D.leaf p ω - D.reference p ω - D.remainder p ω

def integratedNoise [MeasurableSpace P] (μ : Measure P) (ω : Ω) : ℝ := ∫ p, D.noiseVersion p ω ∂μ

end LevelData

variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω] {n : ℕ}

/-- Explicit deterministic conditions, supplied for actual cutoff words
by UniformInsertions and the joint Borel word calculus. -/
structure AnalyticConditions (D : LevelData P Ω n) : Prop where
  variance_measurable : Measurable D.totalVariance
  bounds : ∃ A M h : ℝ, 0 ≤ A ∧ 0 ≤ M ∧ 0 ≤ h ∧
    (∀ z, |D.totalVariance z| ≤ A) ∧ (∀ p, (D.window p).upper ≤ M) ∧
    (∀ p, 0 ≤ (D.window p).left) ∧ (∀ p, (D.window p).right ≤ h)
  tests_uniform : UniformBoundedSmooth D.test
  leaf_measurable : Measurable (fun p : P × Ω => D.leaf p.1 p.2)
  reference_measurable : Measurable (fun p : P × Ω => D.reference p.1 p.2)
  remainder_measurable : Measurable (fun p : P × Ω => D.remainder p.1 p.2)

/-- The remaining stochastic inputs are ordinary finite-dimensional Itô
and centering of its actual martingale term. All covariance, Gaussian
backward-equation, domination and Fubini claims are proved separately. -/
structure ItoConditions (D : LevelData P Ω n) (τ : Measure Ω) : Prop where
  field_measurable : ∀ p, ∀ᵐ ω ∂τ, Measurable (D.field p ω)
  ito : ∀ p, FiniteItoInput τ
    (fun ω => observe (D.state p ω) (D.field p ω) (D.window p).observations)
    (fun ω t => CovarianceMatrix.densityMatrix (fun q => D.totalVariance (D.field p ω q)) (D.window p).observations t)
    (D.window p).left (D.window p).right (D.stochasticTerm p)
  centered : ∀ p, (∫ ω, D.stochasticTerm p (backward (D.window p) (D.test p)) ω ∂τ) = 0

theorem uniform_level_bound (D : LevelData P Ω n) (hD : AnalyticConditions D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ω, ‖D.leaf p ω‖ ≤ K ∧ ‖D.reference p ω‖ ≤ K ∧
      ‖D.remainder p ω‖ ≤ K ∧ ‖D.noiseVersion p ω‖ ≤ K := by
  obtain ⟨A, M, h, hA, hM, hh, ha, hu, hl, hr⟩ := hD.bounds
  obtain ⟨C, hCn, hC⟩ := hD.tests_uniform.norm_bound
  obtain ⟨L, _, hL⟩ := hD.tests_uniform.fderiv.norm_bound
  obtain ⟨B, hBn, hB⟩ := hD.tests_uniform.fderiv.fderiv.norm_bound
  let R : ℝ := ((1 / 2 : ℝ) * (A + M) * B * n) * heatMass h
  have hRn : 0 ≤ R := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA hM)) hBn) (Nat.cast_nonneg _))
    (heatMass_nonneg hh)
  refine ⟨2 * C + R, by positivity, fun p ω => ?_⟩
  have hv : ‖D.leaf p ω‖ ≤ C := hC p _
  have hq : ‖D.reference p ω‖ ≤ C := GaussianSmooth.average_norm_bound _ (hC p) _
  have hr : ‖D.remainder p ω‖ ≤ R := remainder_horizon_bound (D.window p) hA ha hBn (hu p) (hl p) (hr p)
    (D.state p ω) (D.field p ω) ((hD.tests_uniform.smooth p).of_le (by simp)) (hC p) (hL p) (hB p)
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  calc
    _ ≤ (C + C) + R := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hv hq)) hr)
    _ = _ := by ring

theorem noiseVersion_eq_ito (D : LevelData P Ω n) (hD : AnalyticConditions D)
    (τ : Measure Ω) (hIto : ItoConditions D τ) (p : P) :
    D.noiseVersion p =ᵐ[τ] D.stochasticTerm p (backward (D.window p) (D.test p)) := by
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  obtain ⟨A, M, h, hA, hM, hh, ha, hu, hl, hr⟩ := hD.bounds
  have hF := hD.tests_uniform.boundedSmooth p
  obtain ⟨C, hC⟩ := hF.norm_bound
  obtain ⟨L, hL⟩ := hF.fderiv.norm_bound
  obtain ⟨B, hB⟩ := hF.hessian_norm_bound
  obtain ⟨K, hKn, hK⟩ := hF.hessian_lipschitz
  filter_upwards [physical_one_step τ (D.window p) D.totalVariance hD.variance_measurable
    (D.state p) (D.field p) (hIto.field_measurable p) hA ha (D.stochasticTerm p) (hIto.ito p)
    (hF.smooth.of_le (by simp)) hC hL hB ((norm_nonneg (GaussianTaylor.hessian (D.test p) 0)).trans (hB 0)) hKn hK]
    with ω hω
  rw [← PhysicalIto.backward_eq_semigroup (D.window p) (D.test p) ⟨le_rfl, (D.window p).ordered⟩] at hω
  change D.leaf p ω = D.reference p ω + _ + D.remainder p ω at hω
  dsimp only [LevelData.noiseVersion]
  linarith only [hω]

theorem integrated_level (D : LevelData P Ω n) (hD : AnalyticConditions D)
    (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (hIto : ItoConditions D τ) :
    Integrable (D.integratedNoise μ) τ ∧ (∫ ω, D.integratedNoise μ ω ∂τ) = 0 ∧
      (∀ p, D.noiseVersion p =ᵐ[τ] D.stochasticTerm p (backward (D.window p) (D.test p))) ∧
      ∀ ω, (∫ p, D.leaf p ω ∂μ) = (∫ p, D.reference p ω ∂μ) + D.integratedNoise μ ω +
        ∫ p, D.remainder p ω ∂μ := by
  obtain ⟨K, hKn, hK⟩ := uniform_level_bound D hD
  have hNm : Measurable (fun p : P × Ω => D.noiseVersion p.1 p.2) :=
    (hD.leaf_measurable.sub hD.reference_measurable).sub hD.remainder_measurable
  have hNi : Integrable (fun p : P × Ω => D.noiseVersion p.1 p.2) (μ.prod τ) :=
    (integrable_const K).mono' hNm.aestronglyMeasurable (Eventually.of_forall (fun p => (hK p.1 p.2).2.2.2))
  have hNeq := noiseVersion_eq_ito D hD τ hIto
  have hNzero (p : P) : (∫ ω, D.noiseVersion p ω ∂τ) = 0 := by
    rw [integral_congr_ae (hNeq p)]
    exact hIto.centered p
  refine ⟨hNi.integral_prod_right, ?_, hNeq, fun ω => ?_⟩
  · change (∫ ω, ∫ p, D.noiseVersion p ω ∂μ ∂τ) = 0
    rw [← integral_integral_swap hNi]
    simp only [hNzero, integral_zero]
  · have hV : Integrable (fun p => D.leaf p ω) μ := (integrable_const K).mono'
      (hD.leaf_measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun p => (hK p ω).1))
    have hQ : Integrable (fun p => D.reference p ω) μ := (integrable_const K).mono'
      (hD.reference_measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun p => (hK p ω).2.1))
    have hR : Integrable (fun p => D.remainder p ω) μ := (integrable_const K).mono'
      (hD.remainder_measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun p => (hK p ω).2.2.1))
    have he₁ := integral_sub hV hQ
    have he₂ := integral_sub (hV.sub hQ) hR
    simp only [Pi.sub_apply] at he₁ he₂
    change (∫ p, D.leaf p ω ∂μ) = (∫ p, D.reference p ω ∂μ) +
      (∫ p, D.leaf p ω - D.reference p ω - D.remainder p ω ∂μ) + ∫ p, D.remainder p ω ∂μ
    rw [he₂, he₁]
    ring

end SHE.IntegratedPhysicalStep
