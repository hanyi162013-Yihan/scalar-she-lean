module

public import SHE.GaussianRangeSmooth

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Actual singular Gaussian laws are supported on their physical
covariance ranges. The proof uses zero variances, not a chosen eigenbasis. -/
namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianGramScore
  MeasurableGeneralizedInverse
open scoped InnerProductSpace
variable {n : ℕ}

theorem annihilating_map_eq_dirac {A : Mat n} (hA : A.PosSemidef)
    (T : State n →L[ℝ] State n)
    (hT : T.comp (Matrix.toEuclideanCLM (𝕜 := ℝ) A) = 0) :
    (multivariateGaussian (0 : State n) A).map T = Measure.dirac 0 := by
  let μ := multivariateGaussian (0 : State n) A
  have hm : (∫ x : State n, x ∂μ.map T) = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    have hi := T.integral_comp_comm (IsGaussian.integrable_id (μ := μ))
    simpa only [μ, id_eq, integral_id_multivariateGaussian, map_zero] using hi
  have hd := IsGaussian.eq_dirac_of_variance_eq_zero (μ := μ.map T) (fun K => by
    rw [variance_map (by fun_prop) (by fun_prop)]
    let L := K.comp T
    let a := (InnerProductSpace.toDual ℝ (State n)).symm L
    have ha : innerSL ℝ a = L :=
      (InnerProductSpace.toDual ℝ (State n)).apply_symm_apply L
    change Var[L; μ] = 0
    rw [← ha, gaussian_inner_variance hA]
    change (innerSL ℝ a) (Matrix.toEuclideanCLM (𝕜 := ℝ) A a) = 0
    rw [ha]
    change K (T (Matrix.toEuclideanCLM (𝕜 := ℝ) A a)) = 0
    have hz := congrArg (fun B : State n →L[ℝ] State n => B a) hT
    change T (Matrix.toEuclideanCLM (𝕜 := ℝ) A a) = 0 at hz
    rw [hz, map_zero])
  rw [hm] at hd
  exact hd

theorem ae_mem_covariance_range {A : Mat n} (hA : A.PosSemidef) (R : Mat n)
    (hAR : (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range) :
    ∀ᵐ x ∂multivariateGaussian (0 : State n) A,
      x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range := by
  let P := (Matrix.toEuclideanCLM (𝕜 := ℝ) R).comp (generalizedInverse R).toContinuousLinearMap
  let T := ContinuousLinearMap.id ℝ (State n) - P
  have hTA : T.comp (Matrix.toEuclideanCLM (𝕜 := ℝ) A) = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change Matrix.toEuclideanCLM (𝕜 := ℝ) A x -
      Matrix.toEuclideanCLM (𝕜 := ℝ) R (generalizedInverse R (Matrix.toEuclideanCLM (𝕜 := ℝ) A x)) = 0
    have he := generalizedInverse_on_range R (hAR (LinearMap.mem_range_self _ x))
    exact sub_eq_zero.mpr he.symm
  have hd := annihilating_map_eq_dirac hA T hTA
  have hz : ∀ᵐ y ∂(multivariateGaussian (0 : State n) A).map T, y = 0 := by rw [hd]; simp
  have hs : MeasurableSet {y : State n | y = 0} :=
    (isClosed_eq continuous_id continuous_const).measurableSet
  have hz' : ∀ᵐ x ∂multivariateGaussian (0 : State n) A, T x = 0 :=
    (ae_map_iff T.measurable.aemeasurable hs).mp hz
  filter_upwards [hz'] with x hx
  change x - P x = 0 at hx
  have he : x = P x := sub_eq_zero.mp hx
  rw [he]
  exact LinearMap.mem_range_self _ _

theorem ae_mem_own_covariance_range {A : Mat n} (hA : A.PosSemidef) :
    ∀ᵐ x ∂multivariateGaussian (0 : State n) A,
      x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range :=
  ae_mem_covariance_range hA A le_rfl

end SHE.GaussianRangeSmooth
