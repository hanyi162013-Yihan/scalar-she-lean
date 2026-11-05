module

public import SHE.TriangularScoreWords
public import SHE.GaussianFixedScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.GaussianTriangularKernel
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
open TriangularScoreWords SmoothCylinders MeasurableGaussianScores
variable {n : ℕ}

/-- The genuine old/residual Gaussian pair, with the score depending only
on the fixed old vector. No covariance inverse or density is required. -/
def kernel (R B : MeasurableGeneralizedInverse.Mat n) (d : State n) :
    Kernel (State n × State n) n where
  measure := (multivariateGaussian (0 : State n) R).prod (multivariateGaussian 0 B)
  sigmaFinite := inferInstance
  score := fun x => secondScore R d x.1
  score_measurable := by
    have hm : Measurable (fun x : State n × State n => inner ℝ (coefficient R d) x.1) :=
      (innerSL ℝ (coefficient R d)).measurable.comp measurable_fst
    exact (hm.pow_const 2).sub measurable_const
  score_integrable := by
    have hi : Integrable (secondScore R d) (multivariateGaussian (0 : State n) R) :=
      GaussianVectorFractions.gaussian_secondScore_integrable R d
    exact hi.comp_fst (multivariateGaussian (0 : State n) B)
  shift := fun x => x.1 + x.2
  shift_measurable := measurable_fst.add measurable_snd

/-- The kernel is exactly the actual Gaussian Hessian insertion on a
bounded smooth test, with applicability stated in the physical direction. -/
theorem action_eq_hessian {R B : MeasurableGeneralizedInverse.Mat n}
    (hR : R.PosSemidef) (hB : B.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    {F : State n → ℝ} (hF : BoundedSmooth F) (z : State n) :
    (kernel R B d).action F z = WordRecursion.directionalSecond (gaussianAverage (R+B) F) z d := by
  obtain ⟨M, hM⟩ := hF.norm_bound
  have hi := WeightedBorelAverage.integrable (kernel R B d).measure
    (kernel R B d).score (kernel R B d).score_integrable
    (kernel R B d).shift (kernel R B d).shift_measurable F hF.smooth.continuous.measurable
    M (fun w => by simpa only [Real.norm_eq_abs] using hM w) z
  change Integrable (fun x : State n × State n => secondScore R d x.1 * F (z + (x.1 + x.2)))
    ((multivariateGaussian (0 : State n) R).prod (multivariateGaussian 0 B)) at hi
  rw [GaussianFixedScore.hessian_split_score hR hB hF z hd]
  change (∫ x, secondScore R d x.1 * F (z + (x.1 + x.2))
      ∂(multivariateGaussian (0 : State n) R).prod (multivariateGaussian 0 B)) = _
  rw [MeasureTheory.integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro old
  apply integral_congr_ae
  apply ae_of_all
  intro residual
  simp only [add_assoc]
  ring

/-- A newest-coordinate leaf is invariant precisely when the actual
Gaussian pair has no increment in that original coordinate. -/
theorem coordinate_leaf_invariant (R B : MeasurableGeneralizedInverse.Mat n)
    (d : State n) (i : Fin n)
    (hsupport : ∀ᵐ x ∂(kernel R B d).measure, x.1 i + x.2 i = 0)
    (a : ℝ → ℝ) (baseline : ℝ) :
    (kernel R B d).Invariant (fun z => (1 / 2 : ℝ) * (a (z i) - baseline)) := by
  intro z
  filter_upwards [hsupport] with x hx
  change (1 / 2 : ℝ) * (a ((z + (x.1 + x.2)) i) - baseline) = _
  have he : (z + (x.1 + x.2)) i = z i := by
    change z i + (x.1 i + x.2 i) = z i
    rw [hx, add_zero]
  rw [he]

end SHE.GaussianTriangularKernel
