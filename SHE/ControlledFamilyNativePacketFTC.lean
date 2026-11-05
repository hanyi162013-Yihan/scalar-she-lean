module
public import SHE.ControlledFamilyNativeCovarianceLeg
public import SHE.ControlledFamilyNativeMeanPacket
public import SHE.ControlledFamilyNativeKernelPacket
public import SHE.ControlledFamilyNativeRanges
public import SHE.ControlledFamilyNativeResidualFTC
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

namespace SHE.ControlledFamilyNativePacketFTC
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

local notation "WP"=>ControlledFamilyNativeKernelPacket.packet P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "MP"=>ControlledFamilyNativeMeanPacket.packet P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cov"=>ControlledFamilyNativeLegs.covarianceLeg P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "MeanLeg"=>ControlledFamilyNativeLegs.meanLeg P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "BaseLeg"=>ControlledFamilyNativeLegs.baselineLeg P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Joint"=>ControlledJointWeightedWord.jointMeanVector

/-- The exact additive residual in consistent endpoint min clipping is
the covariance-plus-baseline FTC integral of the ORIGINAL native kernel.
Its mean integrability is supplied by the already proved actual cap. -/
theorem residual_all_parameters_ae (hΛ:0≤Λ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier (Base (0,p)) k).terminal h→
      ∀(U D:CircleL2)(E:WordRecursion.State (n+k)),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (R p k h q)).range→
      let V:=PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D
      let mean:=fun θ=>Joint (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ
      ∀a c:ℝ,IntervalIntegrable (fun θ=>MP p k h q θ (mean θ) E V) volume a c→
      IntervalIntegrable (fun θ=>Cov p k h q U D E θ+BaseLeg p k h q U D E θ) volume a c ∧
        WP p k h q c (mean c) E-WP p k h q a (mean a) E-
          (∫θ in a..c,MP p k h q θ (mean θ) E V)=
        ∫θ in a..c,Cov p k h q U D E θ+BaseLeg p k h q U D E θ:=by
  filter_upwards [ControlledFamilyNativeKernelPacket.kernel_eq_packet_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hroot hspan ρ k,
    ControlledFamilyNativeMeanPacket.mean_leg_eq_packet_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hkernel hmean
  intro p q hvq hqt U D E hE V mean a c hMP
  have hV(θ:ℝ):V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (C p k h q θ)).range:=
    ControlledFamilyNativeRanges.damped_direction_mem_range
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hΛ hroot p k h q hvq hqt D θ
  have he:MeanLeg p k h q U D E=(fun θ=>MP p k h q θ (mean θ) E V):=by
    funext θ
    exact hmean p θ q hvq hqt.le U D E hE (hV θ)
  have hi:IntervalIntegrable (MeanLeg p k h q U D E) volume a c:=by
    rw [he]
    exact hMP
  have hh:=ControlledFamilyNativeResidualFTC.residual P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
    hΛ hsmall hroot hspan p k h q hvq hqt U D E hE a c hi
  rw [hkernel p c q hvq hqt U D E hE,hkernel p a q hvq hqt U D E hE,he] at hh
  exact hh

end SHE.ControlledFamilyNativePacketFTC
