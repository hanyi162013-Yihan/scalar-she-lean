module

public import SHE.GaussianScoreChainData
public import SHE.GaussianWordResidual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ProjectedUncutWord
open Set MeasureTheory ProbabilityTheory WordRecursion CutoffWordLevel CutoffWordHistories
open GaussianCoordinates GaussianConvolution TriangularScoreWords MeasurableGaussianScores
open scoped BigOperators
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable {L : CutoffWordLevel.Level R P n}

/-- The fixed-old score average retains every root, rough leaf and
deterministic baseline in the actual original full product. -/
def Chain.oldAverage {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : WordRecursion.State N → ℝ :=
  WeightedBorelAverage.average
    (Measure.pi (fun j => multivariateGaussian (0 : WordRecursion.State N) (chain.old j)))
    (fun x => ∏ j, secondScore (chain.old j) (chain.direction j) (x j))
    (fun x => ∑ j, x j) (TriangularScoreWords.fullTest chain.word chain.initial)

theorem Chain.test_eq_reserved_average {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) (hs : chain.CoordinateSupport) (z : WordRecursion.State N) :
    UncutSmoothWords.test L k p (projection g z) =
      gaussianAverage (∑ j, chain.residual j) chain.oldAverage z := by
  obtain ⟨M,hM⟩ := chain.fullTest_boundedSmooth.norm_bound
  exact (chain.test_eq_pair_integral hs z).trans
    (GaussianWordResidual.pair_word_eq_residual_average chain.old chain.residual
      chain.residual_posSemidef chain.direction (TriangularScoreWords.fullTest chain.word chain.initial)
      chain.fullTest_boundedSmooth.smooth.continuous.measurable M
      (fun w => by simpa only [Real.norm_eq_abs] using hM w) z)

/-- The initial-to-newest Gaussian average is retained for a predictable
word. It joins the reserved covariance; it is not replaced by a current
stochastic state or omitted when estimating the newest rough leaf. -/
theorem Chain.predictable_eq_reserved_average {k : ℕ} {p : History P k}
    {g : Fin (n+k) → Fin N} (chain : Chain L k p g) (hs : chain.CoordinateSupport)
    {C : MeasurableGeneralizedInverse.Mat N} (hC : C.PosSemidef) (z : WordRecursion.State N) :
    gaussianAverage C (fun w => UncutSmoothWords.test L k p (projection g w)) z =
      gaussianAverage (C + ∑ j, chain.residual j) chain.oldAverage z := by
  have he : (fun w => UncutSmoothWords.test L k p (projection g w)) =
      gaussianAverage (∑ j, chain.residual j) chain.oldAverage := by
    funext w
    exact chain.test_eq_reserved_average hs w
  rw [he]
  let μ : Measure (Fin k → WordRecursion.State N) :=
    Measure.pi (fun j => multivariateGaussian 0 (chain.old j))
  let S : (Fin k → WordRecursion.State N) → ℝ :=
    fun x => ∏ j, secondScore (chain.old j) (chain.direction j) (x j)
  let shift : (Fin k → WordRecursion.State N) → WordRecursion.State N := fun x => ∑ j, x j
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
  have hm : Measurable chain.oldAverage := WeightedBorelAverage.measurable μ S hSm shift hshift _ hF
  have hbound : ∀ w, |chain.oldAverage w| ≤ M * ∫ x, |S x| ∂μ :=
    WeightedBorelAverage.bound μ S hS shift hshift _ hF M hMn hb
  exact gaussianAverage_composition C (∑ j, chain.residual j) hC
    (Matrix.posSemidef_sum _ (fun j _ => chain.residual_posSemidef j))
    chain.oldAverage hm hbound z

/-- Same predictable identity on the original growing observation space;
the ambient covariance is restricted by the exact selected coordinates. -/
theorem Chain.original_predictable_eq_reserved_average {k : ℕ} {p : History P k}
    {g : Fin (n+k) → Fin N} (chain : Chain L k p g) (hs : chain.CoordinateSupport)
    {C : MeasurableGeneralizedInverse.Mat N} (hC : C.PosSemidef) (z : WordRecursion.State N) :
    gaussianAverage (C.submatrix g g) (UncutSmoothWords.test L k p) (projection g z) =
      gaussianAverage (C + ∑ j, chain.residual j) chain.oldAverage z := by
  rw [← GaussianCoordinates.average_projection g hC (UncutSmoothWords.test L k p)
    (RecursiveGaussianScores.test_boundedSmooth L k p).smooth.continuous.measurable z]
  exact chain.predictable_eq_reserved_average hs hC z

end SHE.ProjectedUncutWord
