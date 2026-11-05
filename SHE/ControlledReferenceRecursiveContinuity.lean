module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRecursiveContinuity
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceRecursiveContinuity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRecursiveContinuity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRecursiveContinuity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

local notation "R" => referenceData P A hA Λ θ v b hvb
local notation "L" => ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall in
/-- The actual covariance at any finite recursive node is continuous
in both original past-state parameters, including singular covariance
and collisions. The original node stops and heat targets are retained. -/
theorem nodeCovariance_continuous (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ)
    (h : History Unit k×(ℝ×HeatCircle)) :
    Continuous (fun p : Inputs => (L p ε k).nodeCovariance h) := by
  apply Continuous.subtype_mk
  have hc := ControlledReferenceCovariance.covariance_inputs_continuous P hΛ θ v hsmall
    ((L (0,0) ε k).observations.observations h.1) ((L (0,0) ε k).terminal h.1)
    ((L (0,0) ε k).nodeTime_mem h).2 ((L (0,0) ε k).targets_after h.1)
  convert hc using 1
  funext p
  change WordRecursion.covariance (ControlledReferenceWindows.coefficient P Λ θ v p)
    ((L p ε k).observations.observations h.1) ((L p ε k).nodeTime h) ((L p ε k).terminal h.1)=_
  rw [ControlledReferenceRecursiveBounds.observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε k h.1,
    ControlledReferenceRecursiveBounds.nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h,
    ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h.1]

theorem cutoffRow_eq (p p' : Inputs) (ε : ℝ≥0) (k : ℕ)
    (h : History Unit k×(ℝ×HeatCircle)) :
    (L p ε k).cutoffRow δ h=(L p' ε k).cutoffRow δ h := by
  classical
  have hg : (L p ε k).Good δ h ↔ (L p' ε k).Good δ h := by
    change ((v:ℝ)<h.2.1 ∧ h.2.1≤(L p ε k).terminal h.1-δ) ↔
      ((v:ℝ)<h.2.1 ∧ h.2.1≤(L p' ε k).terminal h.1-δ)
    rw [ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε ε k h.1]
  by_cases hp : (L p ε k).Good δ h
  · have hp' := hg.mp hp
    simp only [CutoffWordLevel.Level.cutoffRow,hp,hp',ite_true]
    rw [ControlledReferenceRecursiveBounds.observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε k h.1,
      ControlledReferenceRecursiveBounds.nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε ε k h]
  · have hp' : ¬(L p' ε k).Good δ h := fun hh => hp (hg.mpr hh)
    simp only [CutoffWordLevel.Level.cutoffRow,hp,hp',ite_false]

include hsmall in
/-- The genuinely moving finite recursive word is jointly continuous
in both past-state inputs and its finite-dimensional argument. This is
not continuity for a fixed test substituted into a random reference. -/
theorem continuous_test (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) => (L q.1 ε k).test h q.2) := by
  induction k with
  | zero => exact hF.smooth.continuous.comp continuous_snd
  | succ k ih =>
    let G : Inputs→WordRecursion.State (n+k)→ℝ := fun p => (L p ε k).test h.1
    have hG := ih h.1
    have hGs := uniform_reindex
      (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k)
      (fun p : Inputs => (p,(ε,h.1)))
    have hC := nodeCovariance_continuous P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h
    have hH := GaussianParameterContinuity.continuous_average_hessian G hG hGs
      (fun p : Inputs => (L p ε k).nodeCovariance h) hC
    have hp : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
        (q.1,SmoothWords.tailProjection (n+k) q.2)) :=
      continuous_fst.prodMk ((SmoothWords.tailProjection (n+k)).continuous.comp continuous_snd)
    have hH' := hH.comp hp
    have hr : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) => (L q.1 ε k).cutoffRow δ h) := by
      have he : (fun q : Inputs×WordRecursion.State (n+(k+1)) => (L q.1 ε k).cutoffRow δ h)=
          fun _ => (L (0,0) ε k).cutoffRow δ h := by
        funext q
        exact cutoffRow_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ q.1 (0,0) ε k h
      rw [he]
      exact continuous_const
    have hd := (hH'.clm_apply hr).clm_apply hr
    have ha := hA.smooth.continuous.comp ((SmoothWords.headProjection (n+k)).continuous.comp
      (continuous_snd : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) => q.2)))
    have href : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
        (R q.1).reference ((L q.1 ε k).nodeTime h,h.2.2)) := by
      have he : (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
          (R q.1).reference ((L q.1 ε k).nodeTime h,h.2.2))=
          fun q => ControlledReferenceWindows.coefficient P Λ θ v q.1 ((L (0,0) ε k).nodeTime h,h.2.2) := by
        funext q
        change ControlledReferenceWindows.coefficient P Λ θ v q.1 ((L q.1 ε k).nodeTime h,h.2.2)=_
        rw [ControlledReferenceRecursiveBounds.nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ q.1 (0,0) ε ε k h]
      rw [he]
      exact (ControlledReferenceWindows.coefficient_inputs_continuous P Λ θ v hΛ hsmall _).comp continuous_fst
    exact (continuous_const.mul (ha.sub href)).mul hd

end SHE.ControlledReferenceRecursiveContinuity
