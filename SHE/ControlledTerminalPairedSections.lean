module

public import SHE.ControlledTerminalPairedAmplitude
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
namespace SHE.ControlledTerminalPairedSections
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
variable (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
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



open HistoryProductMeasure OrderedHeatForests ScalarRootRelativeGeometry
local notation "Sc"=>ControlledTerminalPairedAmplitude.scale P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Amp"=>ControlledTerminalPairedAmplitude.amplitude P hA Λ v b hvb Z htarget hstop F hF hFm

theorem scale_sections
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (k:ℕ) (t:Fin k→ℝ) (x x':HeatCircle) (w w':Fin k→HeatCircle)
    (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    Sc k (separated k (x,t,w)) choices χ A0 ν i=
      Sc k (separated k (x',t,w')) choices χ A0 ν i:=by
  have hl:=FixedHistoryTimeFactors.lower_sections Zero (b:ℝ) (fun _=>rfl) k t x x' w w'
  have hu:=FixedHistoryTimeFactors.upper_sections Zero (b:ℝ) (fun _=>rfl) k t x x' w w'
  have ht:=FixedHistoryTimeFactors.targets_sections Zero (b:ℝ) (fun _=>rfl) (fun _=>(b:ℝ)) hrootage
    k t x x' w w'
  unfold ControlledTerminalPairedAmplitude.scale
  rw [hl,hu,ht]

/-- The genuine paired-slot envelope has ONE fixed time factor and
ONE original translated parent forest. The output point never enters
the minimum-gap chooser or any full-age empty-leaf gain. -/
theorem amplitude_relative
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (k:ℕ) (t:Fin k→ℝ)
    (hp:StrictHistory Zero k (separated k ((0:HeatCircle),t,fun _=>0)))
    (x:HeatCircle) (w:Fin k→HeatCircle)
    (choices:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    Amp k (separated k (x,t,fun j=>w j+x)) choices χ A0 ν i=
      (timeWeight Zero (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k
          (separated k ((0:HeatCircle),t,fun _=>0))*
        |Sc k (separated k ((0:HeatCircle),t,fun _=>0)) choices χ A0 ν i|)*
      parentDensity 2 (by norm_num) k
        (targets Zero k (separated k ((0:HeatCircle),t,fun _=>0)))
        (carrier_orderedTimes Zero hages k _ hp) (values (fun _:Fin 1=>(0:HeatCircle)) k w):=by
  let a:=separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
  let p:=separated k (x,t,fun j=>w j+x)
  have hpx:StrictHistory Zero k p:=
    (FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) (fun _=>rfl) k t x 0 _ (fun _=>0)).mpr hp
  unfold ControlledTerminalPairedAmplitude.amplitude
  rw [FixedHistoryTimeFactors.timeWeight_sections Zero (b:ℝ) (fun _=>rfl)
    (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k t x 0 _ (fun _=>0)]
  rw [scale_sections P hA Λ v b hvb Z htarget hstop F hF hFm hrootage k t x 0 _ (fun _=>0)]
  rw [ParentMeanDensity.parentProduct_eq_parentDensity Zero hages k p hpx]
  change (timeWeight Zero (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k a*
    parentDensity 2 (by norm_num) k (targets Zero k p) (carrier_orderedTimes Zero hages k p hpx)
      (centers Zero k p))*|Sc k a choices χ A0 ν i|=_
  rw [ScalarRootRelativeGeometry.parent_density_relative Zero (b:ℝ) (fun _=>rfl) 2 (by norm_num) (b:ℝ) hrootage hcenter k t x w]
  ring

end SHE.ControlledTerminalPairedSections
