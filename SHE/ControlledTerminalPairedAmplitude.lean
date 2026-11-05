module

public import SHE.PairedTerminalTimeFields
public import SHE.TerminalSuccessorGeometry
public import SHE.ParentMeanDensity
public import SHE.FixedHistoryDomain
public import SHE.ControlledTerminalPairedFields
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledRelativeScoreForest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.ControlledTerminalPairedAmplitude
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalScoreChain
  ControlledFamilyProfileForest SmoothCylinders UniformSmooth CoveredControlledLaw CoveredHistoryGeometry
open PhysicalParentGeometry
open scoped NNReal
local instance controlledTerminalPairedRelative_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledTerminalPairedRelative_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledTerminalPairedRelative_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ) (v b:ℝ≥0) (hvb:v≤b)
variable {X:Type} [MeasurableSpace X] (Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (Function.uncurry F))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "SE" => ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TE" => ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "CE" => ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LE" => ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "UE" => ControlledThetaPhysicalGeometry.upper_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm


def scale (k:ℕ) (h:History X k) (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):ℝ:=
  PairedTerminalTimeFields.factor P (fun j=>lower Zero k h j-(v:ℝ))
    (fun j=>upper Zero k h j-(v:ℝ))
    (fun j=>targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ)) choices χ A0 ν i

def amplitude (k:ℕ) (h:History X k) (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):ℝ:=
  timeWeight Zero (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k h*
    ParentMeanDensity.parentProduct Zero k h*|scale P hA Λ v b hvb Z htarget hstop F hF hFm k h choices χ A0 ν i|

theorem scale_measurable (k:ℕ) (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    Measurable (fun h=>scale P hA Λ v b hvb Z htarget hstop F hF hFm k h choices χ A0 ν i):=
  PairedTerminalTimeFields.factor_measurable P _ _ _
    (fun j=>(lower_measurable Zero k j).sub_const _)
    (fun j=>(upper_measurable Zero k j).sub_const _)
    (fun j=>((carrier Zero k).observations.target_measurable _).sub_const _) choices χ A0 ν i

theorem amplitude_measurable (k:ℕ) (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    Measurable (fun h=>amplitude P hA Λ v b hvb Z htarget hstop F hF hFm k h choices χ A0 ν i):=
  ((FixedHistoryTimeFactors.timeWeight_measurable Zero _ _ k).mul
    (ParentMeanDensity.parentProduct_measurable Zero k)).mul
    (continuous_abs.measurable.comp (scale_measurable P hA Λ v b hvb Z htarget hstop F hF hFm k choices χ A0 ν i))

theorem amplitude_nonneg (k:ℕ) (h:History X k) (hp:StrictHistory Zero k h)
    (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    0≤amplitude P hA Λ v b hvb Z htarget hstop F hF hFm k h choices χ A0 ν i:=by
  apply mul_nonneg
  · exact mul_nonneg (timeWeight_nonneg Zero (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos)
      (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k h hp)
      (ParentMeanDensity.parentProduct_nonneg Zero k h)
  · exact abs_nonneg _

theorem scale_atSpace (k:ℕ) (h:History X (k+1)) (x:HeatCircle)
    (choices:List (Fin (k+1)×Fin (k+2))) (χ A0 ν:ℝ) (i:Fin (k+2)):
    scale P hA Λ v b hvb Z htarget hstop F hF hFm (k+1) (TerminalSuccessorGeometry.atSpace h x) choices χ A0 ν i=
      scale P hA Λ v b hvb Z htarget hstop F hF hFm (k+1) h choices χ A0 ν i:=by
  have ht:targets Zero (k+1) (TerminalSuccessorGeometry.atSpace h x)=targets Zero (k+1) h:=by
    rw [TerminalSuccessorGeometry.targets_succ,TerminalSuccessorGeometry.targets_succ]
    rfl
  unfold scale
  rw [TerminalSuccessorGeometry.lower_atSpace,TerminalSuccessorGeometry.upper_atSpace,ht]

end SHE.ControlledTerminalPairedAmplitude
