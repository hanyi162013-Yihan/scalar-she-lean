module

public import SHE.PairedTimeTranslation
public import SHE.ControlledFiniteEndpointComparison
public import SHE.ControlledMarkTimeShift
public import SHE.ControlledWordTimeShift
public import SHE.MixedPastTerminalRMS

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.ControlledPairedClockShift
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain PhysicalChainArrays CoveredControlledLaw
  ShiftedWordGeometry ShiftedScoreArrays ShiftedPhysicalArrays ControlledProfile
  SmoothCylinders UniformSmooth
open scoped NNReal BigOperators
local instance controlledPairedClockShift_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledPairedClockShift_circleSigma:MeasurableSpace CircleL2:=borel _
local instance controlledPairedClockShift_circleBorel:BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient) (Λ:ℝ)
variable (h:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P P.coefficient hA Λ h Z htarget hstop F hF hFm
local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P P.coefficient hA Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v

local notation "BS"=>ControlledWordTimeShift.base_shift P P.coefficient hA Λ h
local notation "TS"=>ControlledWordTimeShift.terminal_shift P P.coefficient hA Λ h Z htarget hstop F hF hFm
local notation "ZS"=>ControlledWordTimeShift.observations_shift P P.coefficient hA Λ h Z htarget hstop F hF hFm
local notation "RS"=>ControlledWordTimeShift.reference_shift P P.coefficient hA Λ h

/-- Exact clock translation of every literal normalized paired
Gaussian slot. No profile law, rank, or support exception is changed. -/
theorem average_translation (v:ℝ≥0) (p:Inputs) (k:ℕ) (hist:History HeatCircle k)
    (newMean oldMean:WordRecursion.State (1+k)) (cs:List (Fin k×Fin (k+1)))
    (ν χ:ℝ) (i:Fin (k+1)):
    ControlledTerminalPairedFields.average P hA Λ v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm k p (shift (v:ℝ) k hist) newMean oldMean cs ν χ i=
    ControlledTerminalPairedFields.average P hA Λ 0 h bot_le
      Z htarget hstop F hF hFm k p hist newMean oldMean cs ν χ i:=by
  let L:=Rel (0,p)
  let K:=Abs v (0,p)
  have ho:=ControlledMarkTimeShift.oldProfile_translation P Λ v p
  have ha:covariances K ((carrier K k).observations.observations (shift (v:ℝ) k hist))
      (ControlledFamilyProfileForest.oldProfile P Λ v p) k (shift (v:ℝ) k hist)=
      covariances L ((carrier L k).observations.observations hist)
        (ControlledFamilyProfileForest.oldProfile P Λ 0 p) k hist:=by
    rw [ho]
    exact ShiftedScoreArrays.actual_covariances_shift L K (v:ℝ) (BS v (0,p)) (TS v (0,p)) (ZS v (0,p))
      (by norm_num [L,ControlledWordTimeShift.relativeLevel,ControlledReferenceLevel.referenceData]) v.2 _ k hist
  have hd:directions K ((carrier K k).observations.observations (shift (v:ℝ) k hist)) k (shift (v:ℝ) k hist)=
      directions L ((carrier L k).observations.observations hist) k hist:=by
    rw [observations_shift L K (v:ℝ) (BS v (0,p)) (TS v (0,p)) (ZS v (0,p)) k hist]
    exact directions_shift L K (v:ℝ) (BS v (0,p)) (TS v (0,p)) (ZS v (0,p)) _ k hist
  have hB:fullResidualCovariance K (ControlledFamilyProfileForest.oldProfile P Λ v p) k
      (shift (v:ℝ) k hist) ((carrier K k).terminal (shift (v:ℝ) k hist))=
      fullResidualCovariance L (ControlledFamilyProfileForest.oldProfile P Λ 0 p) k hist
        ((carrier L k).terminal hist):=by
    rw [terminal_shift L K (v:ℝ) (BS v (0,p)) (TS v (0,p)) k hist,ho]
    exact fullResidualCovariance_shift L K (v:ℝ) (BS v (0,p)) (TS v (0,p)) (ZS v (0,p)) (RS v (0,p))
      (by norm_num [L,ControlledWordTimeShift.relativeLevel,ControlledReferenceLevel.referenceData]) v.2 _ k hist _
  have hbas(θ:ℝ):baseline (Abs v (θ,p)) k (shift (v:ℝ) k hist)=baseline (Rel (θ,p)) k hist:=
    baseline_shift (Rel (θ,p)) (Abs v (θ,p)) (v:ℝ) (BS v (θ,p)) (TS v (θ,p)) (RS v (θ,p)) k hist
  dsimp only [ControlledTerminalPairedFields.average]
  rw [ha,hd,hB,hbas 1,hbas 0,ShiftedPhysicalArrays.rootParameter_shift]

/-- The complete finite source telescope preserves its literal old
Gaussian law and BOTH own baselines under moving-past translation. -/
theorem paired_translation (v:ℝ≥0) (p:Inputs) (k:ℕ) (hist:History HeatCircle k)
    (newMean oldMean:WordRecursion.State (1+k)) (ν χ:ℝ):
    ControlledFiniteEndpointComparison.paired P hA Λ v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm p k (shift (v:ℝ) k hist) newMean oldMean ν χ=
    ControlledFiniteEndpointComparison.paired P hA Λ 0 h bot_le
      Z htarget hstop F hF hFm p k hist newMean oldMean ν χ:=by
  have hbas(θ:ℝ):baseline (Abs v (θ,p)) k (shift (v:ℝ) k hist)=baseline (Rel (θ,p)) k hist:=
    baseline_shift (Rel (θ,p)) (Abs v (θ,p)) (v:ℝ) (BS v (θ,p)) (TS v (θ,p)) (RS v (θ,p)) k hist
  unfold ControlledFiniteEndpointComparison.paired
  simp_rw [hbas 1,hbas 0,average_translation P hA Λ h Z htarget hstop F hF hFm v p k hist]

end SHE.ControlledPairedClockShift
