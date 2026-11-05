module

public import SHE.RootFiniteGeometry
public import SHE.PhysicalFullResidualScore

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.RootPhysicalGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  SmoothCylinders UniformSmooth CoveredControlledLaw PhysicalScoreChain PhysicalChainArrays
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n N : ℕ}
variable (L : Level R X n) (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
  (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "K"=>RootFiniteSums.withRoot L F hF hFm

theorem lower_eq (k : ℕ) (p : History X k) : lower K k p=lower L k p := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih p.1) i) j
    exact CarrierGeometryCongruence.nodeTime K L rfl (fun _=>rfl) k p

theorem upper_eq (k : ℕ) (p : History X k) : upper K k p=upper L k p := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih p.1) i) j
    exact RootFiniteGeometry.terminal_eq L F hF hFm k p.1

theorem direction_eq (Z : Fin N→Observation) (k : ℕ) (p : History X (k+1)) :
    PhysicalScoreChain.direction K Z k p=PhysicalScoreChain.direction L Z k p := by
  classical
  unfold PhysicalScoreChain.direction
  rw [CarrierGeometryCongruence.interior_iff K L rfl (fun _=>rfl) k p,
    CarrierGeometryCongruence.nodeTime K L rfl (fun _=>rfl) k p]

theorem directions_eq (Z : Fin N→Observation) (k : ℕ) (p : History X k) :
    directions K Z k p=directions L Z k p := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih p.1) i) j
    exact direction_eq L F hF hFm Z k p

theorem covariances_eq (Z : Fin N→Observation) (c : StoppedGaussianFeatures.Domain→ℝ)
    (k : ℕ) (p : History X k) : covariances K Z c k p=covariances L Z c k p := by
  unfold covariances
  rw [lower_eq L F hF hFm k p,upper_eq L F hF hFm k p]

theorem leaves_eq (k : ℕ) (p : History X k) (g : Fin (n+k)→Fin N) :
    leaves K k p g=leaves L k p g := by
  unfold leaves baseline
  rw [lower_eq L F hF hFm k p]

/-- Replacing the root leaves every original centered coefficient
factor, old matrix and score direction unchanged. -/
theorem word_withRoot (k : ℕ) (p : History X k) (g : Fin (n+k)→Fin N) (z : WordRecursion.State N) :
    word K k p g z=F (rootParameter k p) (GaussianCoordinates.projection (rootSelector k g) z)*
      ∏ j : Fin k,leaves L k p g j z := by
  unfold word
  rw [leaves_eq L F hF hFm k p g]
  rfl

theorem fullResidual_eq (c : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (p : History X k) (q : ℝ) :
    fullResidualCovariance K c k p q=fullResidualCovariance L c k p q := by
  unfold fullResidualCovariance
  rw [RootFiniteGeometry.observations_eq L F hF hFm k p,RootFiniteGeometry.terminal_eq L F hF hFm k p,
    covariances_eq L F hF hFm]
end SHE.RootPhysicalGeometry
