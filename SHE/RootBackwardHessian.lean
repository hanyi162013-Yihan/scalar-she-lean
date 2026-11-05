module

public import SHE.RootHeatTestContinuity
public import SHE.ObservationTargetContinuity
public import SHE.PhysicalRemainderMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.RootBackwardHessian
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RootHeatBounds RootHeatTargets CutoffWordAnalytic Filter Topology
open PhysicalIto PhysicalRemainderBound PhysicalRemainderMass
open scoped NNReal
local instance rootBackwardHessian_period : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance rootBackwardHessian_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance rootBackwardHessian_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)
variable (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)

theorem continuous_backward_hessian (k : ℕ) (p : History P k) (t : ℝ) :
    Continuous (fun q : ℝ≥0 × WordRecursion.State (n+k) => GaussianTaylor.hessian
      (GaussianItoTest.backward ((level L δ hδ q.1 k).window p) ((level L δ hδ q.1 k).test p) t) q.2) := by
  have hF := RootHeatTestContinuity.continuous_test L δ hδ k p
  have hFs := CutoffWordLevel.uniform_reindex (test_uniform L δ hδ k) (fun ε : ℝ≥0 => (ε,p))
  have hA := nodeCovariance_continuous L δ hδ k (p,(t,0))
  exact GaussianParameterContinuity.continuous_average_hessian
    (fun ε => (level L δ hδ ε k).test p) hF hFs
    (fun ε => (level L δ hδ ε k).nodeCovariance (p,(t,0))) hA

end SHE.RootBackwardHessian
