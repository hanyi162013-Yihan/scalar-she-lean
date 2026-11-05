module

public import SHE.FullPhysicalWord
public import SHE.PhysicalFullResidualScore

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianCoordinates PhysicalScoreChain SmoothCylinders GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n N : ℕ}
variable (L : Level R X n)

/-- The literal original root/centered-leaf product is genuinely bounded
smooth even before any physical chain has been chosen. -/
theorem word_boundedSmooth (k : ℕ) (p : History X k) (g : Fin (n+k)→Fin N) :
    BoundedSmooth (word L k p g) := by
  classical
  have hl (j : Fin k) : BoundedSmooth (leaves L k p g j):=
    (BoundedSmooth.const (1/2:ℝ)).mul
      ((R.totalVariance_smooth.comp_right (EuclideanSpace.proj (leafIndex k g j))).sub
        (BoundedSmooth.const (baseline L k p j)))
  have hp (s : Finset (Fin k)) : BoundedSmooth (fun z : WordRecursion.State N=>∏ j∈s,leaves L k p g j z) := by
    induction s using Finset.induction_on with
    | empty=>simpa only [Finset.prod_empty] using BoundedSmooth.const (E:=WordRecursion.State N) (1:ℝ)
    | @insert j s hj ih=>simpa only [Finset.prod_insert hj] using (hl j).mul ih
  exact ((L.test_uniform.boundedSmooth (rootParameter k p)).comp_right
    (projection (rootSelector k g))).mul (hp Finset.univ)

/-- All old second scores are integrated with their actual product
Gaussian law; no covariance rank or range condition is required for L¹. -/
theorem old_weight_integrable (c : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (p : History X k) :
    Integrable (fun x : Fin k→WordRecursion.State (n+k)=>∏ j,secondScore
      (covariances L ((carrier L k).observations.observations p) c k p j)
      (directions L ((carrier L k).observations.observations p) k p j) (x j))
      (Measure.pi (fun j=>multivariateGaussian 0
        (covariances L ((carrier L k).observations.observations p) c k p j))) :=
  Integrable.fintype_prod (fun j=>GaussianVectorFractions.gaussian_secondScore_integrable _ _)
end SHE.PhysicalChainArrays
