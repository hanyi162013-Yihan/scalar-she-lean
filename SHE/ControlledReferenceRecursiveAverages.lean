module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.ControlledReferenceRecursiveBackward
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRecursiveAverages
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceRecursiveAverages_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRecursiveAverages_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRecursiveAverages_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

local notation "R" => referenceData P A hA Λ θ v b hvb
local notation "L" => ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

/-- Every derivative bound of the genuinely averaged recursive words
is uniform over both past inputs, heat ages and all finite histories. -/
theorem averagedTest_uniform (k : ℕ) : UniformBoundedSmooth
    (fun q : Inputs×(ℝ≥0×(History Unit k×(ℝ×HeatCircle))) => (L q.1 q.2.1 k).averagedTest q.2.2) := by
  let Q := Inputs×(ℝ≥0×(History Unit k×(ℝ×HeatCircle)))
  have hG := uniform_reindex
    (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k)
    (fun q : Q => (q.1,(q.2.1,q.2.2.1)))
  exact hG.average (fun q : Q => ProbabilityTheory.multivariateGaussian (0 : WordRecursion.State (n+k))
    ((L q.1 q.2.1 k).nodeCovariance q.2.2).val) (fun _ => inferInstance)

include hsmall in
theorem averaged_hessian_continuous (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ)
    (h : History Unit k×(ℝ×HeatCircle)) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) =>
      GaussianTaylor.hessian ((L q.1 ε k).averagedTest h) q.2) := by
  have hFs := uniform_reindex
    (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k)
    (fun p : Inputs => (p,(ε,h.1)))
  exact GaussianParameterContinuity.continuous_average_hessian
    (fun p : Inputs => (L p ε k).test h.1)
    (ControlledReferenceRecursiveContinuity.continuous_test P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h.1)
    hFs (fun p : Inputs => (L p ε k).nodeCovariance h)
    (ControlledReferenceRecursiveContinuity.nodeCovariance_continuous P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h)

end SHE.ControlledReferenceRecursiveAverages
