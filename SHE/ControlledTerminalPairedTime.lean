module

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
namespace SHE.ControlledTerminalPairedTime
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

def amplitude (k:ℕ) (t:Fin k→ℝ) (cs:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):ℝ:=
  if StrictHistory Zero k (MixedPastTerminalSlotSpatial.anchor k t) then TimeAmp k t cs χ A0 ν i else 0

theorem amplitude_measurable (k:ℕ) (cs:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    Measurable (fun t=>amplitude P hA Λ v b hvb Z htarget hstop F hF hFm k t cs χ A0 ν i):=by
  have ha:Measurable (MixedPastTerminalSlotSpatial.anchor (k:=k)):=
    (HistoryProductMeasure.separated_measurable k).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  apply Measurable.ite ((strictHistory_measurableSet Zero k).preimage ha)
    _ measurable_const
  exact ((FixedHistoryTimeFactors.timeWeight_measurable Zero _ _ k).comp ha).mul
    (continuous_abs.measurable.comp ((ControlledTerminalPairedAmplitude.scale_measurable
      P hA Λ v b hvb Z htarget hstop F hF hFm k cs χ A0 ν i).comp ha))

theorem strict_active (k:ℕ) (t:Fin (k+1)→ℝ):
    (StrictHistory Zero (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t) ∧
      (v:ℝ)<(carrier Zero (k+1)).terminal (MixedPastTerminalSlotSpatial.anchor (k+1) t)) ↔
      StrictHistory Zero (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t):=by
  refine ⟨And.left,fun hp=>⟨hp,?_⟩⟩
  change (v:ℝ)<(carrier Zero k).nodeTime (MixedPastTerminalSlotSpatial.anchor (k+1) t)
  have he:(carrier Zero k).nodeTime (MixedPastTerminalSlotSpatial.anchor (k+1) t)=
      (MixedPastTerminalSlotSpatial.anchor (k+1) t).2.1:=ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
  exact hp.2.1.trans_eq he.symm

/-- The TRUE terminal paired rough time amplitude, under original
restricted old-time volume. No gap degree is hidden in a constant. -/
theorem rough_integral (hvb':v<b) (k:ℕ)
    (cs:List (Fin (k+1)×Fin (k+2))) (hc:cs∈assignments (m:=k+2) (List.finRange (k+1)))
    (j0:Fin (k+1)) {χ A0 ν:ℝ} (hχ:0≤χ) (hχβ:χ<P.exponent) (hA0:0≤A0) (hν:0≤ν):
    Integrable (fun t=>amplitude P hA Λ v b hvb Z htarget hstop F hF hFm (k+1) t cs χ A0 ν j0.succ)
      (Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))) ∧
    (∫t,amplitude P hA Λ v b hvb Z htarget hstop F hF hFm (k+1) t cs χ A0 ν j0.succ
      ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))≤
      scorePrefactor (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) (k+1)*
        PairedPhysicalGapScale.prefactor P cs j0 χ A0*
        ((((k+1)+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc (pairedDegree P.exponent χ j0))*
        ((b:ℝ)-(v:ℝ))^(((k+1:ℕ):ℝ)*P.exponent/4-χ/4)*
        rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) ((b:ℝ)-(v:ℝ))^
          (AllocatedAssignmentKernel.rootCount cs):=by
  have hh:=TerminalPairedGapIntegrals.rough_integral Zero P (b:ℝ) (fun _=>rfl) le_rfl
    (show (v:ℝ)<(b:ℝ) from by exact_mod_cast hvb')
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (uniformConstant 1)
    (fun j=>(uniformConstant_pos 1 j).le) (k+1) (0:HeatCircle) (fun _=>0) cs hc j0 hχ hχβ hA0 hν
  have he:(fun t=>amplitude P hA Λ v b hvb Z htarget hstop F hF hFm (k+1) t cs χ A0 ν j0.succ)=
      (fun t:Fin (k+1)→ℝ=>
        let h:=HistoryProductMeasure.separated (k+1) ((0:HeatCircle),t,fun _=>0)
        if StrictHistory Zero (k+1) h ∧ (v:ℝ)<(carrier Zero (k+1)).terminal h then
          timeWeight Zero (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) (k+1) h*
            |PairedTerminalTimeFields.factor P (fun j=>lower Zero (k+1) h j-(v:ℝ))
              (fun j=>upper Zero (k+1) h j-(v:ℝ))
              (fun j=>targets Zero (k+1) h (leafIndex (k+1) (fun i:Fin (1+(k+1))=>i) j)-(v:ℝ))
              cs χ A0 ν j0.succ| else 0):=by
    funext t
    by_cases hp:StrictHistory Zero (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t)
    · have hc:=(strict_active P hA Λ v b hvb Z htarget hstop F hF hFm k t).mpr hp
      dsimp only [MixedPastTerminalSlotSpatial.anchor] at hp hc
      simp only [amplitude,if_pos hp,if_pos hc,MixedPastTerminalSlotSpatial.timeAmplitude,
        ControlledTerminalPairedAmplitude.scale,MixedPastTerminalSlotSpatial.anchor]
    · have hc:¬(StrictHistory Zero (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t) ∧
          (v:ℝ)<(carrier Zero (k+1)).terminal (MixedPastTerminalSlotSpatial.anchor (k+1) t)):=fun h=>hp h.1
      dsimp only [MixedPastTerminalSlotSpatial.anchor] at hp hc
      simp only [amplitude,if_neg hp,if_neg hc,MixedPastTerminalSlotSpatial.anchor]
  rw [he]
  exact hh

/-- The actual paired root amplitude retains the FULL N rough gain. -/
theorem root_integral (hvb':v<b) (k:ℕ)
    (cs:List (Fin (k+1)×Fin (k+2))) (hc:cs∈assignments (m:=k+2) (List.finRange (k+1)))
    {χ A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν):
    Integrable (fun t=>amplitude P hA Λ v b hvb Z htarget hstop F hF hFm (k+1) t cs χ A0 ν 0)
      (Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))) ∧
    (∫t,amplitude P hA Λ v b hvb Z htarget hstop F hF hFm (k+1) t cs χ A0 ν 0
      ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))≤
      2*scorePrefactor (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) (k+1)*
        PhysicalAssignmentGapScale.prefactor P cs A0 1*
        ((((k+1)+1:ℕ):ℝ)^2*AllocatedAssignmentKernel.inverseDegreeProduct cs hc (P.exponent/4))*
        ((b:ℝ)-(v:ℝ))^(((k+1:ℕ):ℝ)*P.exponent/4)*
        rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) ((b:ℝ)-(v:ℝ))^
          (AllocatedAssignmentKernel.rootCount cs):=by
  have hh:=TerminalRootTimeIntegral.root_integral Zero P (b:ℝ) (fun _=>rfl) le_rfl
    (show (v:ℝ)<(b:ℝ) from by exact_mod_cast hvb')
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (uniformConstant 1)
    (fun j=>(uniformConstant_pos 1 j).le) (k+1) (0:HeatCircle) (fun _=>0) cs hc hA0 hν (χ:=χ)
  have he:(fun t=>amplitude P hA Λ v b hvb Z htarget hstop F hF hFm (k+1) t cs χ A0 ν 0)=
      (fun t:Fin (k+1)→ℝ=>
        let h:=HistoryProductMeasure.separated (k+1) ((0:HeatCircle),t,fun _=>0)
        if StrictHistory Zero (k+1) h ∧ (v:ℝ)<(carrier Zero (k+1)).terminal h then
          timeWeight Zero (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) (k+1) h*
            |PairedTerminalTimeFields.factor P (fun j=>lower Zero (k+1) h j-(v:ℝ))
              (fun j=>upper Zero (k+1) h j-(v:ℝ))
              (fun j=>targets Zero (k+1) h (leafIndex (k+1) (fun i:Fin (1+(k+1))=>i) j)-(v:ℝ))
              cs χ A0 ν 0| else 0):=by
    funext t
    by_cases hp:StrictHistory Zero (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t)
    · have hc:=(strict_active P hA Λ v b hvb Z htarget hstop F hF hFm k t).mpr hp
      dsimp only [MixedPastTerminalSlotSpatial.anchor] at hp hc
      simp only [amplitude,if_pos hp,if_pos hc,MixedPastTerminalSlotSpatial.timeAmplitude,
        ControlledTerminalPairedAmplitude.scale,MixedPastTerminalSlotSpatial.anchor]
    · have hc:¬(StrictHistory Zero (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t) ∧
          (v:ℝ)<(carrier Zero (k+1)).terminal (MixedPastTerminalSlotSpatial.anchor (k+1) t)):=fun h=>hp h.1
      dsimp only [MixedPastTerminalSlotSpatial.anchor] at hp hc
      simp only [amplitude,if_neg hp,if_neg hc,MixedPastTerminalSlotSpatial.anchor]
  rw [he]
  exact hh

end SHE.ControlledTerminalPairedTime
