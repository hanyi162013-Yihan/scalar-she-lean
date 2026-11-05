module
public import SHE.ControlledFamilyNativeLegs
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

namespace SHE.ControlledFamilyNativeResidualFTC
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

local notation "Kernel"=>ControlledFamilyNativeDirection.kernel P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mark"=>ControlledFamilyNativeDirection.mark P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cov"=>ControlledFamilyNativeLegs.covarianceLeg P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "MeanLeg"=>ControlledFamilyNativeLegs.meanLeg P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "BaseLeg"=>ControlledFamilyNativeLegs.baselineLeg P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- The additive A residual is the FULL native endpoint difference
minus its literal mean packet integral. Only the mean integrability is
needed to separate it from the already integrable complete mark. -/
theorem residual (hΛ:0≤Λ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(p:Inputs)(k:ℕ)(h:History X k)
    (q:ℝ)(hvq:(v:ℝ)≤q)(hqt:q<(carrier (Base (0,p)) k).terminal h)
    (U D:CircleL2)(E:WordRecursion.State (n+k))
    (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
      (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)))).range)
    (a c:ℝ)(hMean:IntervalIntegrable (MeanLeg p k h q U D E) volume a c):
    IntervalIntegrable (fun θ=>Cov p k h q U D E θ+BaseLeg p k h q U D E θ) volume a c ∧
      Kernel p k h q U D E c-Kernel p k h q U D E a-
        (∫θ in a..c,MeanLeg p k h q U D E θ)=
      ∫θ in a..c,Cov p k h q U D E θ+BaseLeg p k h q U D E θ:=by
  have ht:=(ControlledFamilyNativeDirection.transfer P A hA Λ v b hvb Z htarget hstop F hF hFm
    hΛ hsmall hroot hspan p k h q hvq hqt U D E hE).2 a c
  have he:(fun θ=>Cov p k h q U D E θ+BaseLeg p k h q U D E θ)=
      (fun θ=>Mark p k h q U D E θ-MeanLeg p k h q U D E θ):=by
    funext θ
    rw [ControlledFamilyNativeLegs.mark_eq]
    ring
  rw [he]
  refine ⟨ht.1.sub hMean,?_⟩
  rw [intervalIntegral.integral_sub ht.1 hMean,ht.2]

end SHE.ControlledFamilyNativeResidualFTC
