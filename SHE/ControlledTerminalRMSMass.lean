module

public import SHE.MixedPastTerminalRMS
public import SHE.PairedRMSTimeBudget
public import SHE.TerminalPairedGapIntegrals
public import SHE.TerminalRootTimeIntegral
public import SHE.MixedPastTerminalSlotSpatial
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
namespace SHE.ControlledTerminalRMSMass
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
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
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


open GaussianAssignmentBlocks HeterogeneousAssignmentKernel PhysicalAssignmentGapScale Classical Real
local notation "TimeAmp"=>MixedPastTerminalSlotSpatial.timeAmplitude Λ P hA v b hvb Z htarget hstop F hF hFm


variable (κ M:ℝ)
local notation "RMS"=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=hA) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
local notation "Ai"=>ControlledTerminalPairedTime.amplitude P hA Λ v b hvb Z htarget hstop F hF hFm

/-- Actual original old-time RMS mass is bounded by the EXPLICIT finite
root/rough budget; the full N-beta gain and all root clips are retained. -/
theorem mass_bound (hvb':v<b) (k:ℕ) {χ A0 ν:ℝ} (hχ:0≤χ) (hχβ:χ<P.exponent)
    (hA0:0≤A0) (hν:0≤ν) (order:ℕ) (B0:ℝ≥0):
    (∫t,RMS (k+1) t ν χ A0 order B0
      ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))≤
      PairedRMSTimeBudget.total P κ M (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
        (k+1) ((b:ℝ)-(v:ℝ)) χ A0 ν order B0:=by
  let cs:=GaussianAssignmentBlocks.assignments (m:=k+2) (List.finRange (k+1))
  let η:=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
  have hi(c:Fin cs.length)(i:Fin (k+2)):
      Integrable (fun t=>Ai (k+1) t (cs.get c) χ A0 ν i) η:=by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (ControlledTerminalPairedTime.root_integral P hA Λ v b hvb Z htarget hstop F hF hFm
        hvb' k (cs.get c) (List.get_mem cs c) hA0 hν).1
    · exact (ControlledTerminalPairedTime.rough_integral P hA Λ v b hvb Z htarget hstop F hF hFm
        hvb' k (cs.get c) (List.get_mem cs c) j hχ hχβ hA0 hν).1
  have hb(c:Fin cs.length)(i:Fin (k+2)):
      (∫t,Ai (k+1) t (cs.get c) χ A0 ν i ∂η)≤
      PairedRMSTimeBudget.mass P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
        (cs.get c) (List.get_mem cs c) ((b:ℝ)-(v:ℝ)) χ A0 ν i:=by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (ControlledTerminalPairedTime.root_integral P hA Λ v b hvb Z htarget hstop F hF hFm
        hvb' k (cs.get c) (List.get_mem cs c) hA0 hν).2
    · exact (ControlledTerminalPairedTime.rough_integral P hA Λ v b hvb Z htarget hstop F hF hFm
        hvb' k (cs.get c) (List.get_mem cs c) j hχ hχβ hA0 hν).2
  unfold MixedPastTerminalRMS.amplitude PairedRMSTimeBudget.total
  rw [integral_const_mul,integral_finsetSum _ (fun i _=>(hi i.1 i.2).const_mul _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hb i.1 i.2) (sqrt_nonneg _)

end SHE.ControlledTerminalRMSMass
