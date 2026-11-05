module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.UncutSmoothWords
public import SHE.UncutHistoryMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceUncutBounds
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceUncutBounds_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceUncutBounds_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceUncutBounds_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
local notation "Base" => ControlledReferenceLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF

theorem carrier_terminal_eq (p p' : Inputs) (k : ℕ) (h : History Unit k) :
    (CutoffCarriers.carrier (Base p) k).terminal h=(CutoffCarriers.carrier (Base p') k).terminal h :=
  ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF 1 zero_lt_one p p' 0 0 k h

theorem carrier_nodeTime_eq (p p' : Inputs) (k : ℕ) (h : History Unit k×(ℝ×HeatCircle)) :
    (CutoffCarriers.carrier (Base p) k).nodeTime h=(CutoffCarriers.carrier (Base p') k).nodeTime h :=
  ControlledReferenceRecursiveBounds.nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF 1 zero_lt_one p p' 0 0 k h

theorem carrier_observations_eq (p p' : Inputs) (k : ℕ) (h : History Unit k) :
    (CutoffCarriers.carrier (Base p) k).observations.observations h=(CutoffCarriers.carrier (Base p') k).observations.observations h :=
  ControlledReferenceRecursiveBounds.observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF 1 zero_lt_one p p' 0 k h

/-- The genuine uncut history row depends on original stops, targets
and spatial centers, and is independent of the random reference input. -/
theorem row_eq (p p' : Inputs) (k : ℕ) (h : History Unit k×(ℝ×HeatCircle)) :
    CutoffCarriers.row (Base p) k h=CutoffCarriers.row (Base p') k h := by
  classical
  have hg : CutoffCarriers.Interior (Base p) k h ↔ CutoffCarriers.Interior (Base p') k h := by
    change ((v:ℝ)<h.2.1 ∧ h.2.1<(CutoffCarriers.carrier (Base p) k).terminal h.1) ↔
      ((v:ℝ)<h.2.1 ∧ h.2.1<(CutoffCarriers.carrier (Base p') k).terminal h.1)
    rw [carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF p p' k h.1]
  by_cases hp : CutoffCarriers.Interior (Base p) k h
  · have hp' := hg.mp hp
    simp only [CutoffCarriers.row,hp,hp',ite_true]
    rw [carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF p p' k h.1,
      carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF p p' k h]
  · have hp' : ¬CutoffCarriers.Interior (Base p') k h := fun hh => hp (hg.mpr hh)
    simp only [CutoffCarriers.row,hp,hp',ite_false]

theorem weight_eq (p p' : Inputs) (k : ℕ) (h : History Unit k) :
    UncutSmoothWords.weight (Base p) k h=UncutSmoothWords.weight (Base p') k h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change UncutSmoothWords.weight (Base p) k h.1*‖CutoffCarriers.row (Base p) k h‖^2=
      UncutSmoothWords.weight (Base p') k h.1*‖CutoffCarriers.row (Base p') k h‖^2
    rw [ih h.1,row_eq P A hA Λ θ v b hvb Z htarget hstop F hF p p' k h]

/-- Fixed smooth-depth derivative constants for the true normalized
UNCUT words are uniform in BOTH past states. There is no positive
time cutoff in this statement. -/
theorem normalized_uniform (k : ℕ) : UniformBoundedSmooth
    (fun q : Inputs×History Unit k => UncutSmoothWords.normalized (Base q.1) k q.2) := by
  induction k with
  | zero => exact UniformBoundedSmooth.fixed hF
  | succ k ih =>
    let Q := Inputs×(History Unit k×(ℝ×HeatCircle))
    have hG := (uniform_reindex ih (fun q : Q => (q.1,q.2.1))).average
      (fun q : Q => ProbabilityTheory.multivariateGaussian (0 : WordRecursion.State (n+k))
        ((CutoffCarriers.carrier (Base q.1) k).nodeCovariance q.2).val) (fun _ => inferInstance)
    exact core_uniform hA hG
      (fun q : Q => ControlledReferenceWindows.coefficient P Λ θ v q.1
        ((CutoffCarriers.carrier (Base q.1) k).nodeTime q.2,q.2.2.2))
      (fun q : Q => NormalizedInsertion.unitRow (CutoffCarriers.row (Base q.1) k q.2))
      P.upper_nonneg (fun q => ControlledReferenceWindows.coefficient_abs_bound P Λ θ v q.1 _)
      zero_le_one (fun _ => NormalizedInsertion.norm_unitRow_le _)

/-- The actual uncut tests have a genuine integrable heat-history
weight, with the smooth-depth constant uniform over the random inputs. -/
theorem test_norm_bound (k : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) (h : History Unit k) z,
    ‖UncutSmoothWords.test (Base p) k h z‖≤C*UncutSmoothWords.weight (Base (0,0)) k h := by
  obtain ⟨C,hCn,hC⟩ := (normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF k).norm_bound
  refine ⟨C,hCn,fun p h z => ?_⟩
  rw [UncutSmoothWords.test_eq_weight_normalized,Pi.smul_apply,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base p) k h)]
  rw [weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF p (0,0) k h]
  exact mul_le_mul_of_nonneg_left (hC (p,h) z) (UncutSmoothWords.weight_nonneg (Base (0,0)) k h) |>.trans_eq (by ring)

end SHE.ControlledReferenceUncutBounds
