module

public import SHE.ControlledThetaRelativeDerivative
public import SHE.ControlledThetaRelativeWord
public import SHE.ControlledThetaStoppedCovariance
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

namespace SHE.ControlledThetaRelativeArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaRelativeArrays_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeArrays_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeArrays_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm



local notation "Zero" => Base (0,(0,0))


local notation "SE" => ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TE" => ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "CE" => ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LE" => ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "UE" => ControlledThetaPhysicalGeometry.upper_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "COVE" => ControlledThetaPhysicalGeometry.covariances_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

/-- Fixed deterministic physical arrays name every actual old law,
while its reference profile retains the genuine varying past inputs. -/
theorem old_covariance_relative_fixed (p : ℝ×Inputs) (k : ℕ) (h : History X k)
    {q : ℝ} (hvq : (v:ℝ) ≤ q) (hqt : q ≤ (carrier Zero k).terminal h) :
    covariances Zero ((carrier Zero k).observations.observations h) (oldProfile P Λ v p.2) k h=
      OldIntervalCovariance.familyCovariance
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (referenceProfile P Λ p.2.1 p.2.2) (fun j=>lower Zero k h j-(v:ℝ))
        (fun j=>upper Zero k h j-(v:ℝ)) := by
  have hqt' : q ≤ (carrier (Base p) k).terminal h:=by rwa [TME p (0,(0,0)) k h]
  have he:=ControlledThetaRelativeWord.old_covariance_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt'
  rw [OME p (0,(0,0)) k h,COVE p (0,(0,0)),SE p (0,(0,0)) k h,TE p (0,(0,0)) k h,
    CE p (0,(0,0)) k h,LE p (0,(0,0)) k h,UE p (0,(0,0)) k h] at he
  exact he

/-- The full fresh residual uses the same deterministic relative
geometry on one history event before every interpolation/past input. -/
theorem full_covariance_relative_fixed_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,0 ≤ q → q ≤ (carrier Zero k).terminal h →
      fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q=
      ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
        (fixedProfile P Λ p.2.1 p.2.2 (fun j=>lower Zero k h j-(v:ℝ))
          (fun j=>upper Zero k h j-(v:ℝ)))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
        (centers Zero k h) (q-(v:ℝ)) p.1 := by
  filter_upwards [ControlledThetaStoppedCovariance.relative_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hq hqt
  have hqt' : q ≤ (carrier (Base p) k).terminal h:=by rwa [TME p (0,(0,0)) k h]
  have he:=hh p q hq hqt'
  simpa only [SE p (0,(0,0)) k h,TE p (0,(0,0)) k h,CE p (0,(0,0)) k h,
    LE p (0,(0,0)) k h,UE p (0,(0,0)) k h] using he

end SHE.ControlledThetaRelativeArrays
