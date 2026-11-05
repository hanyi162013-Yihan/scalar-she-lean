module
public import SHE.ControlledFamilyNativeDirection
public import SHE.ControlledFamilyThreeLeg
public import SHE.NativeDirectionKernelFTC

public import SHE.ControlledThetaStoppedCovariance
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyNativeLegs
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyThreeLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyThreeLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyThreeLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Sig" => ControlledFamilyThreeLeg.sigma P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Tar" => ControlledFamilyThreeLeg.target P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cen" => ControlledFamilyThreeLeg.center P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Lo" => ControlledFamilyThreeLeg.lo P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Hi" => ControlledFamilyThreeLeg.hi P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP" => ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Law" => ControlledFamilyThreeLeg.oldLaw P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => ControlledFamilyThreeLeg.oldWeight P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => ControlledFamilyThreeLeg.scaledRoot P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => ControlledFamilyThreeLeg.coefficientLeaf A (n:=n)
open ControlledFamilyThreeLeg

def reserve (p:Inputs) (k:ℕ) (h:History X k) (q:ℝ):Matrix (Fin (n+k)) (Fin (n+k)) ℝ:=
  NativeFirstScoreReserve.covariance P (Sig p k h) (Tar p k h)
    (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ))

def remaining (p:Inputs) (k:ℕ) (h:History X k) (q θ:ℝ):Matrix (Fin (n+k)) (Fin (n+k)) ℝ:=
  ControlledFixedReserve.covariance P Λ p.1 p.2
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h)))
    (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)) θ

local notation "R"=>reserve P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "C"=>remaining P A hA Λ v b hvb Z htarget hstop F hF hFm

def average (p:Inputs) (k:ℕ) (h:History X k) (q:ℝ) (E:WordRecursion.State (n+k))
    (G:WordRecursion.State (n+k)→ℝ):WordRecursion.State (n+k)→ℝ:=
  WeightedBorelAverage.average ((Law p k h).prod (multivariateGaussian 0 (R p k h q)))
    (GaussianFixedFirstAverage.weight (R p k h q) E (Wgt p k h))
    (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) G

local notation "Avg"=>average P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mean"=>ControlledJointWeightedWord.jointMeanVector

/-- Exact covariance-profile contribution of the native directional FTC. -/
def covarianceLeg (p:Inputs) (k:ℕ) (h:History X k) (q:ℝ) (U D:CircleL2)
    (E:WordRecursion.State (n+k)) (θ:ℝ):ℝ:=
  ControlledFixedReserve.mark P Λ p.1 p.2
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h)))
    (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ))
    (Avg p k h q E (test Finset.univ (Root p k h) (Leaf k)
      (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ))) θ
    (Mean (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ)

/-- Complete current-mean contribution with all full-profile baselines. -/
def meanLeg (p:Inputs) (k:ℕ) (h:History X k) (q:ℝ) (U D:CircleL2)
    (E:WordRecursion.State (n+k)) (θ:ℝ):ℝ:=
  GaussianRangeSmooth.ProfileReserve.affineMeanMark (C p k h q)
    (Avg p k h q E (test Finset.univ (Root p k h) (Leaf k)
      (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)))
    (PhysicalMeanRange.currentDirection (Tar p k h) (Cen p k h) (q-(v:ℝ)) U)
    (PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D) θ

/-- Every omitted baseline remains under the SAME original old/native
first-score law; its (1/2)^k factor is in the original scaled root. -/
def baselineLeg (p:Inputs) (k:ℕ) (h:History X k) (q:ℝ) (U D:CircleL2)
    (E:WordRecursion.State (n+k)) (θ:ℝ):ℝ:=
  -(∑j:Fin k,ControlledFiniteWord.baselineDerivatives P Λ p.1 p.2 (LP p k h) j θ*
    gaussianAverage (C p k h q θ)
      (Avg p k h q E (test (Finset.univ.erase j) (Root p k h) (Leaf k)
        (fun i=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) i θ)))
      (Mean (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ))

/-- Literal decomposition, before any clipping or random averaging. -/
theorem mark_eq (p:Inputs) (k:ℕ) (h:History X k) (q:ℝ) (U D:CircleL2)
    (E:WordRecursion.State (n+k)) (θ:ℝ):
    ControlledFamilyNativeDirection.mark P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D E θ=
      covarianceLeg P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D E θ+
      meanLeg P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D E θ+
      baselineLeg P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D E θ:=by
  rfl

end SHE.ControlledFamilyNativeLegs
