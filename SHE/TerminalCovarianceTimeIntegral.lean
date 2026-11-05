module

public import SHE.ControlledTerminalCovarianceSections
public import SHE.PastMeanDampedTime
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
namespace SHE.TerminalCovarianceTimeIntegral
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
open HistoryProductMeasure QuarterSpatialEvent Classical
local notation "TA"=>ControlledTerminalCovarianceSections.timeAmplitude
  P hA Λ v b hvb Z htarget hstop F hF hFm

def activeAmplitude (k:ℕ) (A0 ν:ℝ) (t:Fin k→ℝ):ℝ:=
  if StrictHistory Zero k (anchor k t) ∧ (v:ℝ)<(carrier Zero k).terminal (anchor k t)
  then TA k t A0 ν else 0

local notation "AA"=>activeAmplitude P hA Λ v b hvb Z htarget hstop F hF hFm

theorem activeAmplitude_eq (k:ℕ) (A0 ν:ℝ):
    AA k A0 ν=fun t=>PastMeanTimeFactors.totalIntegrand Zero P (fraction P*P.lower)
      (uniformConstant 1) k (v:ℝ) 1 A0 ν (anchor k t)/2:=by
  funext t
  unfold activeAmplitude ControlledTerminalCovarianceSections.timeAmplitude PastMeanTimeFactors.totalIntegrand
  split_ifs <;> simp only [sub_self,Real.rpow_zero,one_mul,zero_div,anchor]

theorem activeAmplitude_measurable (k:ℕ) (A0 ν:ℝ):Measurable (AA k A0 ν):=by
  rw [activeAmplitude_eq P hA Λ v b hvb Z htarget hstop F hF hFm]
  exact ((PastMeanTimeFactors.totalIntegrand_measurable Zero P (fraction P*P.lower)
    (uniformConstant 1) k (v:ℝ) 1 A0 ν).comp (anchor_measurable k)).div_const 2

theorem activeAmplitude_nonneg (k:ℕ) (A0 ν:ℝ) (t:Fin k→ℝ):0≤AA k A0 ν t:=by
  rw [activeAmplitude_eq P hA Λ v b hvb Z htarget hstop F hF hFm]
  exact div_nonneg (PastMeanTimeFactors.totalIntegrand_nonneg Zero P
    (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
    (fun j=>(uniformConstant_pos 1 j).le) k (v:ℝ) 1 A0 ν _) (by norm_num)

/-- The literal terminal covariance time envelope integrates under the
ORIGINAL old-time measure. It keeps the exact finite assignment budget;
there is no normalization of the time cube or loss of a gap power. -/
theorem old_time_integral (hvb':v<b) (k:ℕ) {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν):
    Integrable (AA k A0 ν) (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))) ∧
      (∫t,AA k A0 ν t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))≤
        QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
          k ((b:ℝ)-(v:ℝ)) 0 1 A0 ν/2:=by
  have hh:=PastMeanTimeFactors.old_time_budget Zero P (b:ℝ) (fun _=>rfl)
    (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k
    (q:=(v:ℝ)) (fresh:=1) le_rfl (by exact_mod_cast hvb') le_rfl zero_lt_one le_rfl hA0 hν
  rw [activeAmplitude_eq P hA Λ v b hvb Z htarget hstop F hF hFm]
  refine ⟨hh.1.div_const 2,?_⟩
  rw [integral_div]
  simpa only [ControlledReferenceLevel.referenceData,sub_self] using div_le_div_of_nonneg_right hh.2 (by norm_num : (0:ℝ)≤2)

end SHE.TerminalCovarianceTimeIntegral
