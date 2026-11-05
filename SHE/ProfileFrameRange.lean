module

public import SHE.ProfileMatrixAction
public import SHE.MeasurableGeneralizedInverse

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianProfileMark
open Set MeasureTheory GaussianIncrement MeasurableGeneralizedInverse
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

theorem integral_mem_submodule (μ : Measure X) (S : Submodule ℝ (State n))
    {f : X → State n} (hi : Integrable f μ) (hf : ∀ᵐ x ∂μ, f x ∈ S) :
    (∫ x, f x ∂μ) ∈ S := by
  let T := Sᗮ.orthogonalProjectionOnto
  have hz : T (∫ x, f x ∂μ) = 0 := by
    rw [← T.integral_comp_comm hi]
    apply integral_eq_zero_of_ae
    filter_upwards [hf] with x hx
    exact Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero hx
  have hh := (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hz
  simpa only [Submodule.orthogonal_orthogonal] using hh

/-- Covariance integrals retain every actual subspace containing their
physical rows almost everywhere. -/
theorem profileCovariance_range_le (μ : Measure X) (c : X → ℝ) (v : X → State n)
    (hi : Integrable (fun x => c x • rankMatrix (v x)) μ) (S : Submodule ℝ (State n))
    (hv : ∀ᵐ x ∂μ, v x ∈ S) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ c v)).range ≤ S := by
  rintro y ⟨z, rfl⟩
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ c v) z ∈ S
  rw [profileCovariance_apply μ c v hi z]
  apply integral_mem_submodule μ S
  · have hh := (matrixApply z).integrable_comp hi
    simpa only [map_smul, matrixApply_apply, rankMatrix_apply, smul_smul] using hh
  · filter_upwards [hv] with x hx
    exact S.smul_mem _ hx

private theorem inner_square_integrable (μ : Measure X) (v : X → State n)
    (hv : AEStronglyMeasurable v μ) (hi : Integrable (fun x => ‖v x‖ ^ 2) μ) (a : State n) :
    Integrable (fun x => (inner ℝ a (v x)) ^ 2) μ := by
  apply (hi.const_mul (‖a‖ ^ 2)).mono'
    ((continuous_pow 2).comp_aestronglyMeasurable
      ((innerSL ℝ a).continuous.comp_aestronglyMeasurable hv))
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (inner ℝ a (v x)) ^ 2 ≤ ‖a‖ ^ 2 * ‖v x‖ ^ 2
  have hh := pow_le_pow_left₀ (norm_nonneg (inner ℝ a (v x))) (norm_inner_le_norm a (v x)) 2
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using hh

/-- Almost every physical row lies in the range of its literal unweighted
Gram integral. No point-evaluation representative or rank assumption is
needed. This discharges the fixed-reserve range applicability condition. -/
theorem ae_frame_mem_gram_range (μ : Measure X) (v : X → State n)
    (hv : AEStronglyMeasurable v μ) (henergy : Integrable (fun x => ‖v x‖ ^ 2) μ) :
    ∀ᵐ x ∂μ, v x ∈
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ (fun _ => 1) v)).range := by
  let G := profileCovariance μ (fun _ => 1) v
  have hi : Integrable (fun x => (1 : ℝ) • rankMatrix (v x)) μ :=
    profileCovariance_integrable μ (fun _ => 1) v aestronglyMeasurable_const hv (by simpa using henergy)
  let P := (Matrix.toEuclideanCLM (𝕜 := ℝ) G).comp (generalizedInverse G).toContinuousLinearMap
  let T := ContinuousLinearMap.id ℝ (State n) - P
  have hTG (a : State n) : T (Matrix.toEuclideanCLM (𝕜 := ℝ) G a) = 0 := by
    change Matrix.toEuclideanCLM (𝕜 := ℝ) G a -
      Matrix.toEuclideanCLM (𝕜 := ℝ) G (generalizedInverse G (Matrix.toEuclideanCLM (𝕜 := ℝ) G a)) = 0
    exact sub_eq_zero.mpr (generalizedInverse_on_range G (LinearMap.mem_range_self _ a)).symm
  have hj (j : Fin n) : ∀ᵐ x ∂μ, (T (v x)) j = 0 := by
    let L := (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp T
    let a := (InnerProductSpace.toDual ℝ (State n)).symm L
    have ha : innerSL ℝ a = L := (InnerProductSpace.toDual ℝ (State n)).apply_symm_apply L
    have hq := profileCovariance_quadratic μ (fun _ => 1) v hi a
    have hz : inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) G a) = 0 := by
      change (innerSL ℝ a) (Matrix.toEuclideanCLM (𝕜 := ℝ) G a) = 0
      rw [ha]
      change (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)) (T (Matrix.toEuclideanCLM (𝕜 := ℝ) G a)) = 0
      rw [hTG, map_zero]
    have hi0 : (∫ x, (inner ℝ a (v x)) ^ 2 ∂μ) = 0 := by
      simpa only [one_mul] using hq.symm.trans hz
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (inner ℝ a (v x)))
      (inner_square_integrable μ v hv henergy a)).mp hi0
    filter_upwards [hae] with x hx
    have hx0 : (innerSL ℝ a) (v x) = 0 := sq_eq_zero_iff.mp hx
    rw [ha] at hx0
    change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ j) (T (v x)) = 0 at hx0
    simpa only [EuclideanSpace.basisFun_inner] using hx0
  filter_upwards [ae_all_iff.mpr hj] with x hx
  have hz : T (v x) = 0 := by ext j; exact hx j
  have he : v x = P (v x) := sub_eq_zero.mp hz
  rw [he]
  exact LinearMap.mem_range_self _ _

end SHE.GaussianProfileMark
