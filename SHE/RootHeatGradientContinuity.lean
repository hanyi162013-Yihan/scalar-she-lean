module

public import SHE.RootHeatTestContinuity
public import SHE.ParameterSmoothContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.RootHeatGradientContinuity
open Set MeasureTheory WordRecursion CutoffWordLevel CutoffWordHistories
open RootHeatBounds RootHeatTargets SmoothCylinders SmoothWords UniformSmooth
open scoped NNReal
variable {P:Type*} [MeasurableSpace P] {R:ReferenceData} {n:ℕ}
variable (L:Level R P n)(δ:ℝ)(hδ:0<δ)

/-- The genuine gradient of the entire recursively heat-dependent word
is continuous down to zero heat age, at fixed smooth depth and time
cutoff. The Gaussian reserve is allowed to be singular. -/
theorem continuous_gradient (k:ℕ)(h:History P k)(t:ℝ):
    Continuous (fun z:ℝ≥0×WordRecursion.State (n+k)=>
      fderiv ℝ (GaussianItoTest.backward ((level L δ hδ z.1 k).window h)
        ((level L δ hδ z.1 k).test h) t) z.2):=by
  let F:=fun ε:ℝ≥0=>(level L δ hδ ε k).test h
  have hF:=RootHeatTestContinuity.continuous_test L δ hδ k h
  have hFs:=CutoffWordLevel.uniform_reindex (test_uniform L δ hδ k) (fun ε:ℝ≥0=>(ε,h))
  have hA:=nodeCovariance_continuous L δ hδ k (h,(t,0))
  obtain ⟨C,hC,hCb⟩:=hFs.norm_bound
  have hc:=GaussianParameterContinuity.continuous_average F hF hCb
    (fun ε:ℝ≥0=>(level L δ hδ ε k).nodeCovariance (h,(t,0))) hA
  have hs:=hFs.average
    (fun ε:ℝ≥0=>ProbabilityTheory.multivariateGaussian 0
      ((level L δ hδ ε k).nodeCovariance (h,(t,0))).val) (fun _=>inferInstance)
  obtain ⟨B,hB,hBb⟩:=hs.fderiv.fderiv.norm_bound
  exact ParameterSmoothContinuity.continuous_fderiv _ hc
    (fun ε=>(hs.smooth ε).of_le (by simp)) hB hBb

end SHE.RootHeatGradientContinuity
