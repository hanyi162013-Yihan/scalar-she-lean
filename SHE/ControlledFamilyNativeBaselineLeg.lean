module
public import SHE.ControlledFamilyNativeWordIdentity
public import SHE.ControlledFamilyBaselineLeg
public import SHE.PhysicalNativeOmittedAssignments
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

namespace SHE.ControlledFamilyNativeBaselineLeg
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

local notation "R"=>ControlledFamilyNativeLegs.reserve P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "C"=>ControlledFamilyNativeLegs.remaining P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Avg"=>ControlledFamilyNativeLegs.average P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mean"=>ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- Original erased-leaf average equals the native-family omitted test,
with exactly one original factor (1/2)^k. -/
theorem omitted_average_eq_all_parameters_ae
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀θ q:ℝ,(v:ℝ)≤q→q≤(carrier (Base (0,p)) k).terminal h→
      ∀(mean E:WordRecursion.State (n+k))(j:Fin k),
      nativeOmittedAverage (Base (θ,p)) (oldProfile P Λ v p) k h
        (NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
          (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q)
        (fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q-
          NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
            (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q) E mean j=
      gaussianAverage (C p k h q θ)
        (Avg p k h q E (test (Finset.univ.erase j) (Root p k h) (Leaf k)
          (fun i=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) i θ))) mean:=by
  filter_upwards [ControlledFamilyNativeWordIdentity.remaining_eq_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hc
  intro p θ q hvq hqt mean E j
  unfold nativeOmittedAverage
  rw [hc p θ q hvq hqt,
    ControlledFamilyNativeWordIdentity.reserve_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot,
    ControlledFamilyWordIdentity.old_matrices_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyWordIdentity.old_directions_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyWordIdentity.baseline_eq P A hA Λ v b hvb Z htarget hstop F hF hFm]
  exact (ControlledFamilyBaselineLeg.average_scaled_root (Finset.univ.erase j)
    ((Law p k h).prod (multivariateGaussian 0 (R p k h q)))
    (GaussianFixedFirstAverage.weight (R p k h q) E (Wgt p k h))
    (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) _
    (initial (Base (0,p)) k h (fun i=>i)) (Leaf k) _ ((1/2:ℝ)^k) _).symm

/-- Every original baseline derivative is attached to that SAME physical
omitted average before the random-past input is selected. -/
theorem baseline_leg_eq_physical_all_parameters_ae
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀θ q:ℝ,(v:ℝ)≤q→q≤(carrier (Base (0,p)) k).terminal h→
      ∀(U D:CircleL2)(E:WordRecursion.State (n+k)),
      ControlledFamilyNativeLegs.baselineLeg P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D E θ=
      -(∑j:Fin k,ControlledFiniteWord.baselineDerivatives P Λ p.1 p.2 (LP p k h) j θ*
        nativeOmittedAverage (Base (θ,p)) (oldProfile P Λ v p) k h
          (NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
            (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q)
          (fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q-
            NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
              (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q) E (Mean p k h q U D θ) j):=by
  filter_upwards [omitted_average_eq_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hh
  intro p θ q hvq hqt U D E
  unfold ControlledFamilyNativeLegs.baselineLeg
  rw [←ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact (hh p θ q hvq hqt
    (ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ) E j).symm

end SHE.ControlledFamilyNativeBaselineLeg
