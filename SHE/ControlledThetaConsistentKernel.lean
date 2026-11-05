module

public import SHE.ControlledThetaTwoFreshArrays
public import SHE.ControlledThetaNativeAssignments
public import SHE.TwoFreshCompleteWord
public import SHE.ControlledThetaConsistentNative
public import SHE.NativeFirstWholeComplete
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

namespace SHE.ControlledThetaConsistentKernel
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal BigOperators
local instance controlledThetaConsistentKernel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaConsistentKernel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaConsistentKernel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

/-- The literal complete native kernel at its own profile and current
mean is exactly its conditional consistent endpoint packet. The common
history event is chosen BEFORE every interpolation and random past input. -/
theorem kernel_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q≤(carrier Zero k).terminal h→
      ∀(mean E:WordRecursion.State (n+k)),
      let Rnative:=NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q
      let C:=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative
      let A:=covariances (Base p) ((carrier (Base p) k).observations.observations h) (oldProfile P Λ v p.2) k h
      let D:=directions (Base p) ((carrier (Base p) k).observations.observations h) k h
      GaussianConvolution.gaussianAverage C
        (WeightedBorelAverage.average
          ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
            (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
          (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)))
          (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base p) k h (fun i=>i))) mean=
      NativeFirstWholeComplete.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean
        (directions Zero ((carrier Zero k).observations.observations h) k h) E
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaConsistentNative.assigned_integral_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hchain hh
  intro p q hvq hqt mean E Rnative C A D
  obtain ⟨chain,_,_,hphysical⟩:=hchain p
  rw [native_whole_average_of_chain (Base p) (oldProfile P Λ v p.2) chain hphysical Rnative C E mean]
  unfold NativeFirstWholeComplete.value
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro choices _
  exact hh p q hvq hqt mean E choices

end SHE.ControlledThetaConsistentKernel
