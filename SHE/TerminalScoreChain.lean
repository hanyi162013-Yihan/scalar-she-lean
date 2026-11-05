module

public import SHE.PredictableScoreChain
public import SHE.GaussianFirstSplit

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ProjectedUncutWord
open Set Filter MeasureTheory ProbabilityTheory WordRecursion CutoffWordLevel CutoffWordHistories
  GaussianCoordinates GaussianConvolution TriangularScoreWords MeasurableGaussianScores SmoothCylinders
open scoped BigOperators
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable {L : CutoffWordLevel.Level R P n}

/-- The true terminal derivative of every finite recursive word puts its
first score on the terminal old interval. All preceding fixed old scores
and the complete root/centered-leaf product remain in the same average;
only the residual covariances are combined. -/
theorem Chain.terminal_fderiv_reserved_score {k : ℕ} {p : History P k}
    {g : Fin (n+k) → Fin N} (chain : Chain L k p g) (hs : chain.CoordinateSupport)
    {A B : MeasurableGeneralizedInverse.Mat N} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {d : WordRecursion.State N} (hd : d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (z : WordRecursion.State N) :
    fderiv ℝ (gaussianAverage (A+B) (fun w => UncutSmoothWords.test L k p (projection g w))) z d =
      ∫ old, ∫ residual, chain.oldAverage (z+old+residual)*firstScore A d old
        ∂multivariateGaussian 0 (B+∑ j,chain.residual j) ∂multivariateGaussian 0 A := by
  let μ : Measure (Fin k → WordRecursion.State N) :=
    Measure.pi (fun j => multivariateGaussian 0 (chain.old j))
  let S : (Fin k → WordRecursion.State N) → ℝ :=
    fun x => ∏ j, secondScore (chain.old j) (chain.direction j) (x j)
  let shift : (Fin k → WordRecursion.State N) → WordRecursion.State N := fun x => ∑ j,x j
  have hS : Integrable S μ := Integrable.fintype_prod
    (fun j => GaussianVectorFractions.gaussian_secondScore_integrable (chain.old j) (chain.direction j))
  have hSm : Measurable S := by
    apply Finset.measurable_prod Finset.univ
    intro j _
    have hm : Measurable (fun x : Fin k → WordRecursion.State N =>
        inner ℝ (coefficient (chain.old j) (chain.direction j)) (x j)) :=
      (innerSL ℝ (coefficient (chain.old j) (chain.direction j))).measurable.comp (measurable_pi_apply j)
    exact (hm.pow_const 2).sub measurable_const
  have hshift : Measurable shift := Finset.measurable_sum Finset.univ (fun j _ => measurable_pi_apply j)
  have hF := chain.fullTest_boundedSmooth.smooth.continuous.measurable
  obtain ⟨M,hM⟩ := chain.fullTest_boundedSmooth.norm_bound
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb : ∀ w, |TriangularScoreWords.fullTest chain.word chain.initial w| ≤ M :=
    fun w => by simpa only [Real.norm_eq_abs] using hM w
  have hG : Measurable chain.oldAverage := WeightedBorelAverage.measurable μ S hSm shift hshift _ hF
  have hGb : ∀ w, |chain.oldAverage w| ≤ M*∫ x, |S x| ∂μ :=
    WeightedBorelAverage.bound μ S hS shift hshift _ hF M hMn hb
  have hrep : (fun w => UncutSmoothWords.test L k p (projection g w))=
      gaussianAverage (∑ j,chain.residual j) chain.oldAverage := by
    funext w
    exact chain.test_eq_reserved_average hs w
  exact GaussianFirstSplit.fderiv_reserved hA hB
    (Matrix.posSemidef_sum _ (fun j _ => chain.residual_posSemidef j)) hd
    ((RecursiveGaussianScores.test_boundedSmooth L k p).comp_right (projection g))
    hG _ hGb hrep z

end SHE.ProjectedUncutWord
