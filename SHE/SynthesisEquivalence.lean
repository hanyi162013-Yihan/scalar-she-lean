module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.SynthesisEquivalence
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

omit [CompleteSpace E] [CompleteSpace F] in
theorem injective_of_lower_bound (S : E →L[𝕜] F) (C : ℝ)
    (hbelow : ∀ x, ‖x‖ ≤ C*‖S x‖) : Function.Injective S := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  calc
    _ ≤ C*‖S (x-y)‖ := hbelow _
    _ = 0 := by rw [map_sub,hxy,sub_self,norm_zero,mul_zero]

/-- Exact covariance with an invertible physical multiplier gives an
explicit preimage under the synthesis map. -/
theorem surjective_of_covariance (S : E →L[𝕜] F) (M : F ≃L[𝕜] F)
    (hcov : S ∘L S.adjoint = M.toContinuousLinearMap) : Function.Surjective S := by
  intro y
  refine ⟨S.adjoint (M.symm y),?_⟩
  have hh := congrArg (fun A : F →L[𝕜] F => A (M.symm y)) hcov
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hh

/-- Actual bounded synthesis becomes a continuous linear equivalence
once its Riesz lower bound and invertible covariance are proved. -/
def equivalence (S : E →L[𝕜] F) (M : F ≃L[𝕜] F)
    (hcov : S ∘L S.adjoint = M.toContinuousLinearMap) (C : ℝ)
    (hbelow : ∀ x, ‖x‖ ≤ C*‖S x‖) : E ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective S
    (LinearMap.ker_eq_bot.mpr (injective_of_lower_bound S C hbelow))
    (LinearMap.range_eq_top.mpr (surjective_of_covariance S M hcov))

@[simp] theorem equivalence_apply (S : E →L[𝕜] F) (M : F ≃L[𝕜] F)
    (hcov : S ∘L S.adjoint = M.toContinuousLinearMap) (C : ℝ)
    (hbelow : ∀ x, ‖x‖ ≤ C*‖S x‖) (x : E) : equivalence S M hcov C hbelow x = S x := rfl

theorem inverse_bound (S : E →L[𝕜] F) (M : F ≃L[𝕜] F)
    (hcov : S ∘L S.adjoint = M.toContinuousLinearMap) (C : ℝ)
    (hbelow : ∀ x, ‖x‖ ≤ C*‖S x‖) (y : F) :
    ‖(equivalence S M hcov C hbelow).symm y‖ ≤ C*‖y‖ := by
  have hh := hbelow ((equivalence S M hcov C hbelow).symm y)
  change _ ≤ C*‖equivalence S M hcov C hbelow ((equivalence S M hcov C hbelow).symm y)‖ at hh
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh

/-- An invertible coisometry is a genuine unitary isometry. This avoids
silently identifying a covariance factor with a unitary operator. -/
def isometryOfCoisometry (J : E ≃L[𝕜] F)
    (hJ : J.toContinuousLinearMap ∘L J.toContinuousLinearMap.adjoint = ContinuousLinearMap.id 𝕜 F) :
    E ≃ₗᵢ[𝕜] F where
  __ := J.toLinearEquiv
  norm_map' x := by
    have hi : J.toContinuousLinearMap.adjoint (J x) = x := by
      apply J.injective
      have hh := congrArg (fun A : F →L[𝕜] F => A (J x)) hJ
      exact hh
    have hn := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left J.toContinuousLinearMap x
    change ‖J x‖^2 = RCLike.re (inner 𝕜 (J.toContinuousLinearMap.adjoint (J x)) x) at hn
    rw [hi,inner_self_eq_norm_sq] at hn
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn

theorem comparison_covariance (S : E ≃L[𝕜] F) (R : G ≃L[𝕜] F)
    (hcov : S.toContinuousLinearMap ∘L S.toContinuousLinearMap.adjoint =
      R.toContinuousLinearMap ∘L R.toContinuousLinearMap.adjoint) :
    (R.trans S.symm).toContinuousLinearMap ∘L (R.trans S.symm).toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id 𝕜 E := by
  let A := S.symm.toContinuousLinearMap
  have hinv : A ∘L S.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 E := by
    ext x
    exact S.symm_apply_apply x
  change (A ∘L R.toContinuousLinearMap) ∘L (A ∘L R.toContinuousLinearMap).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp]
  calc
    _ = A ∘L (R.toContinuousLinearMap ∘L R.toContinuousLinearMap.adjoint) ∘L A.adjoint := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = A ∘L (S.toContinuousLinearMap ∘L S.toContinuousLinearMap.adjoint) ∘L A.adjoint := by
      rw [← hcov]
    _ = (A ∘L S.toContinuousLinearMap) ∘L (A ∘L S.toContinuousLinearMap).adjoint := by
      rw [ContinuousLinearMap.adjoint_comp]
      simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [hinv,ContinuousLinearMap.adjoint_id,ContinuousLinearMap.comp_id]

/-- Two genuinely invertible factors with the same covariance differ by
a genuine unitary map between their input Hilbert spaces. -/
def comparison (S : E ≃L[𝕜] F) (R : G ≃L[𝕜] F)
    (hcov : S.toContinuousLinearMap ∘L S.toContinuousLinearMap.adjoint =
      R.toContinuousLinearMap ∘L R.toContinuousLinearMap.adjoint) : G ≃ₗᵢ[𝕜] E :=
  isometryOfCoisometry (R.trans S.symm) (comparison_covariance S R hcov)

@[simp] theorem comparison_apply (S : E ≃L[𝕜] F) (R : G ≃L[𝕜] F)
    (hcov : S.toContinuousLinearMap ∘L S.toContinuousLinearMap.adjoint =
      R.toContinuousLinearMap ∘L R.toContinuousLinearMap.adjoint) (x : G) :
    comparison S R hcov x = S.symm (R x) := rfl

end SHE.SynthesisEquivalence
