module
public import SHE.ControlledReferenceThetaGeometry
public import SHE.JointUncutWordEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ControlledPairedUncutLeafIdentity
open Classical
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers SmoothCylinders UniformSmooth
open scoped NNReal ENNReal
variable {X Ω:Type}[MeasurableSpace X][MeasurableSpace Ω]
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(A:ℝ→ℝ)(hA:BoundedSmooth A)
variable (Λ:ℝ)(v b:ℝ≥0)(hvb:v≤b){n:ℕ}(Z:VariableObservations.Family X n)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State n→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State n=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
variable (U V:Ω×ℝ→CircleL2)(XU XV:Ω×(ℝ×HeatCircle)→ℝ)

/-- Changing the reference covariance leaves the actual physical
observation geometry untouched. This does not identify theta0 joint
noise with the genuine ordinary noise. -/
theorem state_eq (p:ℝ×Inputs)(k:ℕ)(h:History X k)(ω:Ω):
    JointWordAnalytic.state (carrier (Base p) k) Λ U V XU XV h ω ((carrier (Base p) k).terminal h)=
      JointWordAnalytic.state (carrier Zero k) Λ U V XU XV h ω ((carrier Zero k).terminal h):=by
  rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
  unfold JointWordAnalytic.state
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]

/-- Literal own-profile paired terminal words are the difference of the
actual joint leaf and the independently evaluated self-pair ordinary leaf,
including zero extension at every nonstrict history. -/
theorem leaf_difference (p:Inputs)(k:ℕ)(h:History X k)(ω:Ω):
    JointUncutWordEvaluation.leaf (Base (1,p)) Λ U V XU XV k h ω-
      JointUncutWordEvaluation.leaf (Base (0,p)) Λ U U XU XU k h ω=
    if PhysicalParentGeometry.StrictHistory Zero k h then
      UncutSmoothWords.test (Base (1,p)) k h
        (JointWordAnalytic.state (carrier Zero k) Λ U V XU XV h ω ((carrier Zero k).terminal h))-
      UncutSmoothWords.test (Base (0,p)) k h
        (JointWordAnalytic.state (carrier Zero k) Λ U U XU XU h ω ((carrier Zero k).terminal h))
    else 0:=by
  unfold JointUncutWordEvaluation.leaf
  rw [state_eq P A hA Λ v b hvb Z htarget hstop F hF hFm U V XU XV,
    state_eq P A hA Λ v b hvb Z htarget hstop F hF hFm U U XU XU]
  by_cases hh:PhysicalParentGeometry.StrictHistory Zero k h
  · rw [if_pos hh]
  · rw [if_neg hh]
    have hz:=PhysicalParentGeometry.weight_zero_of_not_strict Zero k h hh
    have hw(θ:ℝ):UncutSmoothWords.weight (Base (θ,p)) k h=0:=
      (ControlledReferenceThetaGeometry.weight_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
        (θ,p) (0,(0,0)) k h).trans hz
    simp only [UncutSmoothWords.test_eq_weight_normalized,hw,zero_smul,Pi.zero_apply,sub_self]
end SHE.ControlledPairedUncutLeafIdentity
