module

public import SHE.BoundedPhysicalWord
public import SHE.PredictablePhysicalFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianCoordinates PhysicalScoreChain SmoothCylinders GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- The actual fixed-old average has a genuine global state cap,
including singular old covariances and all original rough baselines. -/
theorem oldAverage_bounded (c : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (p : History X k) :
    ∃ B : ℝ,0≤B ∧ ∀ z,|oldAverage L c k p z|≤B := by
  let A:=covariances L ((carrier L k).observations.observations p) c k p
  let D:=directions L ((carrier L k).observations.observations p) k p
  let ν:=Measure.pi (fun j : Fin k=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))
  let W:=fun x : Fin k→WordRecursion.State (n+k)=>∏ j,secondScore (A j) (D j) (x j)
  let shift:=fun x : Fin k→WordRecursion.State (n+k)=>∑ j,x j
  have hi : Integrable W ν:=old_weight_integrable L c k p
  have hs : Measurable shift:=Finset.measurable_sum Finset.univ (fun j _=>measurable_pi_apply j)
  obtain ⟨M,hM⟩:=(word_boundedSmooth L k p (fun i=>i)).norm_bound
  have hM0 : 0≤M:=(norm_nonneg _).trans (hM 0)
  refine ⟨M*∫ x,|W x| ∂ν,mul_nonneg hM0 (integral_nonneg (fun _=>abs_nonneg _)),fun z=>?_⟩
  exact WeightedBorelAverage.bound ν W hi shift hs _
    (word_boundedSmooth L k p (fun i=>i)).smooth.continuous.measurable M hM0
    (fun w=>by simpa only [Real.norm_eq_abs] using hM w) z
end SHE.PhysicalChainArrays
