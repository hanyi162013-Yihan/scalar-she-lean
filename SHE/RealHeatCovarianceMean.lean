module

public import SHE.HeatCovarianceMean
public import SHE.MeasurableGaussianScores
public import SHE.ScalarRange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual real Gaussian mean scores retain the true complex Fourier heat
projection of their sole signed physical input. The score field itself is
the canonical Borel rank-varying matrix score, so its spatial integration
does not assume a measurable Riesz representative. -/
namespace SHE.RealHeatCovarianceMean
open Set MeasureTheory AddCircle Real HeatTorus HeatTorusKernel HeatProjection
  GaussianIncrement GaussianGramScore MeasurableGaussianScores ScalarRange
open scoped InnerProductSpace

variable {n : ℕ}

theorem real_inner_eq_complex_re {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [InnerProductSpace ℂ H] (x y : H) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  exact (re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (𝕜 := ℂ) x y).symm

def meanDirection (S : State n →ₗ[ℝ] CircleL2) (d : CircleL2) : State n :=
  (InnerProductSpace.toDual ℝ (State n)).symm
    ((innerSL ℝ d).comp S.toContinuousLinearMap)

theorem inner_meanDirection (S : State n →ₗ[ℝ] CircleL2) (d : CircleL2) (z : State n) :
    inner ℝ z (meanDirection S d) = (inner ℂ (S z) d).re := by
  rw [real_inner_comm]
  have h := congrArg (fun L : State n →L[ℝ] ℝ => L z)
    ((InnerProductSpace.toDual ℝ (State n)).apply_symm_apply ((innerSL ℝ d).comp S.toContinuousLinearMap))
  change inner ℝ (meanDirection S d) z = inner ℝ d (S z) at h
  rw [h, real_inner_comm, real_inner_eq_complex_re]

theorem meanDirection_apply (S : State n →ₗ[ℝ] CircleL2) (d : CircleL2) (i : Fin n) :
    meanDirection S d i = (inner ℂ (S (EuclideanSpace.basisFun (Fin n) ℝ i)) d).re := by
  rw [← EuclideanSpace.basisFun_inner (Fin n) ℝ (meanDirection S d) i]
  exact inner_meanDirection S d _

theorem meanDirection_measurable {X : Type*} [MeasurableSpace X]
    (S : X → State n →ₗ[ℝ] CircleL2)
    (hS : ∀ i, StronglyMeasurable (fun x => S x (EuclideanSpace.basisFun (Fin n) ℝ i)))
    (d : CircleL2) : Measurable (fun x => meanDirection (S x) d) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have h := ((hS i).inner (𝕜 := ℂ) (stronglyMeasurable_const :
    StronglyMeasurable (fun _ : X => d))).measurable
  have hr := Complex.continuous_re.measurable.comp h
  convert! hr using 1
  funext x
  exact meanDirection_apply (S x) d i

theorem mean_representer_projection_bound {D G : Type*}
    [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    {q : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle)
    (S : D →ₗ[ℝ] CircleL2) (C : D →ₗ[ℝ] G) [CompleteSpace C.range]
    (hspan : ∀ z, S z ∈ heatSpan t a) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ z, ‖S z‖ ≤ L * ‖C z‖) (d : CircleL2) :
    ∃ m ∈ C.range, (∀ z, inner ℝ (C z) m = (inner ℂ (S z) d).re) ∧
      ‖m‖ ≤ L * ‖(heatSpan t a).starProjection d‖ := by
  let _ : InnerProductSpace ℝ (heatSpan t a) :=
    InnerProductSpace.rclikeToReal ℂ (heatSpan t a)
  let _ : NormedSpace ℝ (heatSpan t a) :=
    (InnerProductSpace.rclikeToReal ℂ (heatSpan t a)).toNormedSpace
  let S' : D →ₗ[ℝ] heatSpan t a :=
    { toFun := fun z => ⟨S z, hspan z⟩
      map_add' := fun z w => Subtype.ext (map_add S z w)
      map_smul' := fun b z => Subtype.ext (map_smul S b z) }
  obtain ⟨T, hT, hTC, _⟩ := ScalarRange.factorization_of_bound C S' hL hbound
  let d' : heatSpan t a := (heatSpan t a).orthogonalProjectionOnto d
  obtain ⟨m, hm, hp, hn⟩ := ScalarRange.adjoint_representer C.range T d'
  refine ⟨m, hm, ?_, ?_⟩
  · intro z
    rw [hp _ (LinearMap.mem_range_self C z), hTC, real_inner_eq_complex_re]
    exact congrArg Complex.re ((heatSpan t a).inner_orthogonalProjectionOnto_eq_of_mem_left (S' z) d)
  · exact hn.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg d'))

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The literal canonical real Gaussian score variance is bounded by the
actual signed-input projection energy, including singular Gram matrices. -/
theorem scoreVariance_projection_bound {q : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle)
    (S : State n →ₗ[ℝ] CircleL2) (v : Fin n → G)
    (hspan : ∀ z, S z ∈ heatSpan t a) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ z, ‖S z‖ ≤ L * ‖featureSynthesis v z‖) (d : CircleL2) :
    meanDirection S d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v)).range ∧
    scoreVariance (Matrix.gram ℝ v) (meanDirection S d) ≤
      L ^ 2 * ‖(heatSpan t a).starProjection d‖ ^ 2 := by
  obtain ⟨m, hm, hp, hn⟩ := mean_representer_projection_bound t a S (featureSynthesis v) hspan hL hbound d
  have hpair (z : State n) : inner ℝ (featureSynthesis v z) m = inner ℝ z (meanDirection S d) :=
    (hp z).trans (inner_meanDirection S d z).symm
  refine ⟨physical_direction_mem_range v hm hpair, ?_⟩
  rw [physical_scoreVariance_eq v hm hpair]
  exact (sq_le_sq₀ (norm_nonneg m) (mul_nonneg hL (norm_nonneg _))).mpr hn |>.trans_eq (mul_pow _ _ 2)

/-- Genuine spatial integration of the canonical varying-covariance real
Gaussian score. Only the actual covariance entries and physical heat rows
need be measurable; no chosen score representative field is assumed. -/
theorem translated_scoreVariance_bound (q : ℕ) :
    ∃ h K θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧ 0 < θ ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ (w M : ℝ), 0 < w → 1 ≤ M → (∀ i, w ≤ t i) → (∀ i, t i ≤ M * w) →
      ∀ {n : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
      (v : UnitAddCircle → Fin n → G) (S : UnitAddCircle → State n →ₗ[ℝ] CircleL2),
      Measurable (fun x => Matrix.gram ℝ (v x)) →
      (∀ i, StronglyMeasurable (fun x => S x (EuclideanSpace.basisFun (Fin n) ℝ i))) →
      ∀ (L : ℝ), 0 ≤ L →
      (∀ x z, S x z ∈ heatSpan t (fun i => a i + x)) →
      (∀ x z, ‖S x z‖ ≤ L * ‖featureSynthesis (v x) z‖) →
      ∀ d : CircleL2,
      Integrable (fun x => scoreVariance (Matrix.gram ℝ (v x)) (meanDirection (S x) d)) haarAddCircle ∧
      (∫ x, scoreVariance (Matrix.gram ℝ (v x)) (meanDirection (S x) d) ∂haarAddCircle) ≤
        K * L ^ 2 * sqrt M * sqrt w * ‖CircleHeat.heat (θ * w) d‖ ^ 2 := by
  obtain ⟨h, K, θ, hh, hh1, hK, hθ, hproj⟩ := translated_heat_span_projection_bound q
  refine ⟨h, K, θ, hh, hh1, hK, hθ, ?_⟩
  intro t a ht hth w M hw hM hlo hhi n G _ _ _ v S hcov hS L hL hspan hbound d
  obtain ⟨hpi, hpb⟩ := hproj t a ht hth w M hw hM hlo hhi d
  have hpt (x : UnitAddCircle) := scoreVariance_projection_bound t (fun i => a i + x)
    (S x) (v x) (hspan x) hL (hbound x) d
  have hm := scoreVariance_measurable.comp (hcov.prodMk (meanDirection_measurable S hS d))
  have hi : Integrable (fun x => scoreVariance (Matrix.gram ℝ (v x)) (meanDirection (S x) d)) haarAddCircle := by
    apply (hpi.const_mul (L ^ 2)).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro x
    change ‖scoreVariance (Matrix.gram ℝ (v x)) (meanDirection (S x) d)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (scoreVariance_nonneg (Matrix.posSemidef_gram ℝ (v x)) (hpt x).1)]
    exact (hpt x).2
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, L ^ 2 * ‖(heatSpan t (fun i => a i + x)).starProjection d‖ ^ 2 ∂haarAddCircle :=
      integral_mono hi (hpi.const_mul _) (fun x => (hpt x).2)
    _ = L ^ 2 * (∫ x, ‖(heatSpan t (fun i => a i + x)).starProjection d‖ ^ 2 ∂haarAddCircle) :=
      integral_const_mul _ _
    _ ≤ L ^ 2 * (K * sqrt M * sqrt w * ‖CircleHeat.heat (θ * w) d‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hpb (sq_nonneg _)
    _ = _ := by ring

end SHE.RealHeatCovarianceMean
