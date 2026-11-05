module
public import SHE.ControlledFamilyNativeCovarianceLeg
public import SHE.ControlledThetaConsistentKernel
public import SHE.ControlledFamilyNativeKernelValue
public import SHE.ControlledFamilyActualTransfer
public import SHE.ObservationMarkTimeShift
public import SHE.ControlledFamilyResidualIdentity
public import SHE.ControlledThetaTwoFreshArrays
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

namespace SHE.ControlledFamilyNativeKernelPacket
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyThreeLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyThreeLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyThreeLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Sig" => ControlledFamilyThreeLeg.sigma P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Tar" => ControlledFamilyThreeLeg.target P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cen" => ControlledFamilyThreeLeg.center P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Lo" => ControlledFamilyThreeLeg.lo P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Hi" => ControlledFamilyThreeLeg.hi P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP" => ControlledFamilyThreeLeg.leafPoint P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Law" => ControlledFamilyThreeLeg.oldLaw P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => ControlledFamilyThreeLeg.oldWeight P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => ControlledFamilyThreeLeg.scaledRoot P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => ControlledFamilyThreeLeg.coefficientLeaf P.coefficient (n:=n)
open ControlledFamilyThreeLeg

local notation "R"=>ControlledFamilyNativeLegs.reserve P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "C"=>ControlledFamilyNativeLegs.remaining P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Avg"=>ControlledFamilyNativeLegs.average P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mean"=>ControlledFamilyActualTransfer.mean P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))
local notation "Kernel"=>ControlledFamilyNativeDirection.kernel P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

def packet (p:Inputs) (k:ℕ) (h:History X k) (q θ:ℝ)
    (mean E:WordRecursion.State (n+k)):ℝ:=
  NativeFirstWholeComplete.value P Λ p.1 p.2 θ (q-(v:ℝ))
    (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
    (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean
    (directions Zero ((carrier Zero k).observations.observations h) k h) E
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h))

/-- The endpoint differentiated in the native-family FTC is the SAME
complete consistent packet used by the sharp clipping estimate. -/
theorem kernel_eq_packet_all_parameters_ae
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀θ q:ℝ,(v:ℝ)≤q→q<(carrier (Base (0,p)) k).terminal h→
      ∀(U D:CircleL2)(E:WordRecursion.State (n+k)),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (R p k h q)).range→
      Kernel p k h q U D E θ=
        packet P hA Λ v b hvb Z htarget hstop F hF hFm p k h q θ
          (ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ) E:=by
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=by
    intro x i
    rw [hroot x i]
    exact htarget x i
  filter_upwards [ControlledFamilyNativeWordIdentity.remaining_eq_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k,
    ControlledThetaConsistentKernel.kernel_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hc hs
  intro p θ q hvq hqt U D E hE
  have hqt0:q≤(carrier Zero k).terminal h:=by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm (0,(0,0)) (0,p) k]
    exact hqt.le
  have he:=hs (θ,p) q hvq hqt0
    (ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ) E
  change gaussianAverage
    (fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q-
      NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
        (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q)
    (ControlledFamilyNativeCovarianceLeg.physicalAverage P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p θ k h q E)
    (ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ)=_ at he
  rw [hc p θ q hvq hqt.le,
    ControlledFamilyNativeCovarianceLeg.physicalAverage_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hroot] at he
  rw [ControlledFamilyNativeKernelValue.kernel_eq_average P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
    hroot hspan p k h q hvq hqt U D E hE θ]
  exact he

end SHE.ControlledFamilyNativeKernelPacket
