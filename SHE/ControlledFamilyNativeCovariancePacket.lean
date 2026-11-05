module
public import SHE.ControlledFamilyNativeCovarianceLeg
public import SHE.ControlledThetaNativeCovariance
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

namespace SHE.ControlledFamilyNativeCovariancePacket
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
local notation "Leg"=>ControlledFamilyNativeLegs.covarianceLeg P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

def packet (p:Inputs) (k:ℕ) (h:History X k) (q θ:ℝ)
    (mean E:WordRecursion.State (n+k)):ℝ:=
  (1/2:ℝ)*∫x,ControlledProfile.derivative P Λ p.1 p.2 (x,θ)*
    TwoFreshCompleteWord.value P Λ p.1 p.2 θ (q-(v:ℝ))
      (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
      (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean true
      (directions Zero ((carrier Zero k).observations.observations h) k h) E
      (StoppedGaussianFeatures.stoppedRow (fun i=>stops Zero k h i-(v:ℝ))
        (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h) x)
      (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h))
        ∂StoppedGaussianFeatures.historyMeasure (q-(v:ℝ))

/-- Exact packet to which the native profile A moment/energy estimates
apply; no new profile-mark estimate is assumed at the family interface. -/
theorem covariance_leg_eq_packet_all_parameters_ae
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀θ q:ℝ,(v:ℝ)≤q→q<(carrier (Base (0,p)) k).terminal h→
      ∀(U D:CircleL2)(E:WordRecursion.State (n+k)),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (R p k h q)).range→
      Leg p k h q U D E θ=
        packet P hA Λ v b hvb Z htarget hstop F hF hFm p k h q θ (Mean p k h q U D θ) E:=by
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=by
    intro x i
    rw [hroot x i]
    exact htarget x i
  filter_upwards [ControlledFamilyNativeCovarianceLeg.covariance_leg_eq_physical_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k,
    ControlledThetaNativeCovariance.mark_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hp hs
  intro p θ q hvq hqt U D E hE
  have hqt0:q<(carrier Zero k).terminal h:=by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm (0,(0,0)) (0,p) k]
    exact hqt
  have hE0:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
      (stops (Base (θ,p)) k h) (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q)).range:=by
    rw [ControlledFamilyNativeWordIdentity.reserve_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hroot]
    exact hE
  exact (hp p θ q hvq hqt.le U D E).trans (hs (θ,p) q hvq hqt0 (Mean p k h q U D θ) E hE0
    (fun x=>ControlledProfile.derivative P Λ p.1 p.2 (x,θ)))

end SHE.ControlledFamilyNativeCovariancePacket
