module

public import SHE.ControlledFamilyThreeLeg
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyWordIdentity
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyWordIdentity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyWordIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyWordIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Mat" => ControlledFamilyThreeLeg.oldMatrices P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Dir" => ControlledFamilyThreeLeg.oldDirections P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP" => ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => ControlledFamilyThreeLeg.scaledRoot P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => ControlledFamilyThreeLeg.coefficientLeaf A (n:=n)
local notation "Law" => ControlledFamilyThreeLeg.oldLaw P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => ControlledFamilyThreeLeg.oldWeight P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem old_matrices_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    covariances (Base (θ,p)) ((carrier (Base (θ,p)) k).observations.observations h)
      (oldProfile P Λ v p) k h=Mat p k h := by
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
    (θ,p) (0,p) k]
  exact ControlledThetaPhysicalGeometry.covariances_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
    (θ,p) (0,p) _ _ k h

theorem old_directions_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    directions (Base (θ,p)) ((carrier (Base (θ,p)) k).observations.observations h) k h=Dir p k h := by
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
    (θ,p) (0,p) k]
  exact ControlledThetaPhysicalGeometry.directions_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
    (θ,p) (0,p) _ k h

theorem baseline_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    baseline (Base (θ,p)) k h=ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) (θ:=θ) := by
  funext j
  unfold baseline
  rw [ControlledThetaPhysicalGeometry.lower_eq P A hA Λ v b hvb Z htarget hstop F hF hFm (θ,p) (0,p) k h]
  rfl

theorem word_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    word (Base (θ,p)) k h (fun i=>i)=
      test Finset.univ (Root p k h) (Leaf k)
        (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ) := by
  funext z
  rw [word_eq_centered,baseline_eq P A hA Λ v b hvb Z htarget hstop F hF hFm]
  change (1/2:ℝ)^k*(PhysicalChainArrays.initial (Base (0,p)) k h (fun i=>i) z*
    ∏ j : Fin k,(A (z (leafIndex k (fun i=>i) j))-
      ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ))=
    ((1/2:ℝ)^k*PhysicalChainArrays.initial (Base (0,p)) k h (fun i=>i) z)*
      ∏ j : Fin k,(A (z (leafIndex k (fun i=>i) j))-
        ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)
  ring

theorem old_average_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    oldAverage (Base (θ,p)) (oldProfile P Λ v p) k h=
      WeightedBorelAverage.average (Law p k h) (Wgt p k h) (fun y=>∑ j,y j)
        (test Finset.univ (Root p k h) (Leaf k)
          (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)) := by
  unfold oldAverage
  rw [old_matrices_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    old_directions_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    word_eq P A hA Λ v b hvb Z htarget hstop F hF hFm]
  rfl

end SHE.ControlledFamilyWordIdentity
