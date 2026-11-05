module

public import SHE.ControlledThetaTwoFreshArrays
public import SHE.ControlledThetaNativeAssignments
public import SHE.NativeOmittedCompleteWord
public import SHE.ControlledThetaRelativeNativeOmitted
public import SHE.NativeFirstOmittedPointwise
public import SHE.ControlledThetaAssigned
public import SHE.VaryingFullResidualMoments
public import SHE.ControlledThetaSupported
public import SHE.FullResidualStoppedCovariance
public import SHE.ControlledProfileTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledThetaCompleteNativeOmitted
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaCompleteNativeOmitted_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaCompleteNativeOmitted_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaCompleteNativeOmitted_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

/-- The actual physical complete native-score assignment sum is the
literal complete conditional Gaussian word, on ONE original-history
event for all interpolation/past parameters and all current directions. -/
theorem integral_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q≤(carrier Zero k).terminal h→
      ∀(mean:WordRecursion.State (n+k)) (E:WordRecursion.State (n+k)) (j0:Fin k),
      let Rnative:=NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q
      let C:=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative
      nativeOmittedAverage (Base p) (oldProfile P Λ v p.2) k h Rnative C E mean j0=
      NativeOmittedCompleteWord.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean
        (directions Zero ((carrier Zero k).observations.observations h) k h) E j0
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
  filter_upwards [ControlledThetaRelativeNativeOmitted.omitted_integral_all_parameters_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaNativeAssignments.omitted_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh hactual
  intro p q hvq hqt mean E j0 Rnative C
  rw [hactual p Rnative C E mean j0]
  unfold NativeOmittedCompleteWord.value
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro choices _
  exact hh p q hvq hqt mean E choices j0

end SHE.ControlledThetaCompleteNativeOmitted
