module

public import SHE.MixedPastTerminalCovarianceFields
public import SHE.ScalarRootSharpSections
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
namespace SHE.ControlledTerminalCovarianceSections
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalScoreChain
  ControlledFamilyProfileForest SmoothCylinders UniformSmooth CoveredControlledLaw CoveredHistoryGeometry
open PhysicalParentGeometry ControlledOldIntervals
open scoped NNReal
local instance controlledTerminalPairedRelative_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledTerminalPairedRelative_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledTerminalPairedRelative_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ) (v b:ℝ≥0) (hvb:v≤b)
variable (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "SE" => ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TE" => ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "CE" => ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LE" => ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "UE" => ControlledThetaPhysicalGeometry.upper_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm



open HistoryProductMeasure OrderedHeatForests ScalarRootRelativeGeometry
local notation "Tot"=>PastWordTimeFields.total Zero P
local notation "Amp"=>MixedPastTerminalCovarianceFields.amplitude Λ P hA v b hvb Z htarget hstop F hF hFm

def timeAmplitude (k:ℕ) (t:Fin k→ℝ) (A0 ν:ℝ):ℝ:=
  let a:=separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
  timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*Tot k a A0 ν/2

theorem total_sections
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (k:ℕ) (t:Fin k→ℝ) (x x':HeatCircle) (w w':Fin k→HeatCircle) (A0 ν:ℝ):
    Tot k (separated k (x,t,w)) A0 ν=Tot k (separated k (x',t,w')) A0 ν:=by
  unfold PastWordTimeFields.total
  rw [FixedHistoryTimeFactors.lower_sections Zero (b:ℝ) (fun _=>rfl) k t x x' w w',
    FixedHistoryTimeFactors.upper_sections Zero (b:ℝ) (fun _=>rfl) k t x x' w w',
    FixedHistoryTimeFactors.targets_sections Zero (b:ℝ) (fun _=>rfl) (fun _=>(b:ℝ)) hrootage k t x x' w w']

/-- The actual covariance envelope retains the genuine positive original
parent forest exactly ONCE and an output-independent time amplitude. -/
theorem amplitude_relative
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (k:ℕ) (t:Fin k→ℝ)
    (hp:StrictHistory Zero k (separated k ((0:HeatCircle),t,fun _=>0)))
    (x:HeatCircle) (w:Fin k→HeatCircle) (A0 ν:ℝ):
    Amp k (separated k (x,t,fun j=>w j+x)) A0 ν=
      timeAmplitude P hA Λ v b hvb Z htarget hstop F hF hFm k t A0 ν*
      parentDensity 2 (by norm_num) k
        (targets Zero k (separated k ((0:HeatCircle),t,fun _=>0)))
        (carrier_orderedTimes Zero hages k _ hp) (values (fun _:Fin 1=>(0:HeatCircle)) k w):=by
  let a:=separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
  let p:=separated k (x,t,fun j=>w j+x)
  have hpx:StrictHistory Zero k p:=
    (FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) (fun _=>rfl) k t x 0 _ (fun _=>0)).mpr hp
  have htw:0≤timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k p:=
    timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
      (fun j=>(uniformConstant_pos 1 j).le) k p hpx
  unfold MixedPastTerminalCovarianceFields.amplitude
  rw [abs_of_nonneg (mul_nonneg htw (ParentMeanDensity.parentProduct_nonneg Zero k p))]
  rw [FixedHistoryTimeFactors.timeWeight_sections Zero (b:ℝ) (fun _=>rfl)
    (fraction P*P.lower) (uniformConstant 1) k t x 0 _ (fun _=>0)]
  rw [total_sections P hA Λ v b hvb Z htarget hstop F hF hFm hrootage k t x 0 _ (fun _=>0)]
  rw [ParentMeanDensity.parentProduct_eq_parentDensity Zero hages k p hpx]
  change (timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*
    parentDensity 2 (by norm_num) k (targets Zero k p) (carrier_orderedTimes Zero hages k p hpx)
      (centers Zero k p))*Tot k a A0 ν/2=_
  rw [ScalarRootRelativeGeometry.parent_density_relative Zero (b:ℝ) (fun _=>rfl) 2 (by norm_num)
    (b:ℝ) hrootage hcenter k t x w]
  change _=(timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*Tot k a A0 ν/2)*_
  ring

end SHE.ControlledTerminalCovarianceSections
