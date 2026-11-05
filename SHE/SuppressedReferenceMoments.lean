module

public import SHE.SuppressedGaussianLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.SuppressedReferenceMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianCenteredLeafMoments SuppressedGaussianLaw GaussianReferenceLeafMoments
open scoped BigOperators NNReal
variable {n r : ℕ}

/-- An actual suppressed old/residual leaf retains the full Gaussian
reference baseline. Both the reduced marginal law and its variance
domination are proved from the original Gaussian product. -/
theorem reference_leaf_even_moment (is : List (Fin r))
    (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j, (A j).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) (i : Fin n)
    (a : ℝ → ℝ) (ha : Measurable a) (M H β : ℝ) (hM : ∀ z, |a z| ≤ M)
    (hH : 0 ≤ H) (hβ : 0 ≤ β) (hholder : ∀ z w, |a z-a w| ≤ H*|z-w|^β)
    (m : ℝ) (p : ℕ) :
    let full := ((∑ j, A j) + B) i i
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let F := fun x : (Fin r → State n) × State n =>
      a (m + ((∑ j, suppress is x.1 j) + x.2) i) -
        GaussianProfile.gaussianAverage a m full
    Integrable (fun x => |F x|^(2*p)) μ ∧
      (∫ x, |F x|^(2*p) ∂μ) ≤ leafMomentConstant p β*(H*full^(β/2))^(2*p) := by
  intro full μ F
  have hfull : 0 ≤ full :=
    ((Matrix.posSemidef_sum _ (fun j _ => hA j)).add hB).diag_nonneg
  have hv : (covariance is A B i i).toNNReal ≤ full.toNNReal :=
    Real.toNNReal_le_toNNReal (coordinate_domination is A hA B i)
  have hXm : Measurable (fun x : (Fin r → State n) × State n =>
      ((∑ j, suppress is x.1 j) + x.2) i) := by
    simp_rw [suppress_apply]
    fun_prop
  have hh := reference_baseline_even_moment μ _ hXm (coordinate_hasLaw is A hA B hB i)
    hv a ha M H β hM hH hβ hholder m p
  simpa only [Real.coe_toNNReal _ hfull] using hh

end SHE.SuppressedReferenceMoments
