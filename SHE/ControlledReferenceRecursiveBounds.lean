module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRecursiveBounds
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceRecursiveBounds_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRecursiveBounds_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRecursiveBounds_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

/-- The actual recursively heat-regularized insertion words for each
member of the canonical controlled reference family. The past input
parameter changes the reference at EVERY depth. -/
def level (p : Inputs) (ε : ℝ≥0) (k : ℕ) :
    Level (referenceData P A hA Λ θ v b hvb p) (History Unit k) (n+k) :=
  RecursiveHeatBounds.level (ControlledReferenceLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF p) δ hδ ε k

def test (k : ℕ) (q : Inputs×(ℝ≥0×History Unit k)) : WordRecursion.State (n+k)→ℝ :=
  (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ q.1 q.2.1 k).test q.2.2

/-- At each fixed depth and time cutoff, ALL state-derivative bounds
are uniform over both original past inputs, all histories and the
separate heat-regularization age. No random-profile derivative bound
is assumed. -/
theorem test_uniform (k : ℕ) :
    UniformBoundedSmooth (test P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k) := by
  induction k with
  | zero => exact UniformBoundedSmooth.fixed hF
  | succ k ih =>
    let Q := Inputs×(ℝ≥0×History Unit (k+1))
    let old : Q→Inputs×(ℝ≥0×History Unit k) := fun q => (q.1,(q.2.1,q.2.2.1))
    let hp : Q→History Unit k×(ℝ×HeatCircle) := fun q => q.2.2
    have hG := (uniform_reindex ih old).average
      (fun q : Q => ProbabilityTheory.multivariateGaussian (0 : WordRecursion.State (n+k))
        ((level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ q.1 q.2.1 k).nodeCovariance (hp q)).val)
      (fun _ => inferInstance)
    exact core_uniform hA hG
      (fun q : Q => (referenceData P A hA Λ θ v b hvb q.1).reference
        ((level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ q.1 q.2.1 k).nodeTime (hp q),(hp q).2.2))
      (fun q : Q => (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ q.1 q.2.1 k).cutoffRow δ (hp q))
      P.upper_nonneg (fun q => ControlledReferenceWindows.coefficient_abs_bound P Λ θ v q.1 _)
      (mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos hδ).le)
      (fun q => (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ q.1 q.2.1 k).cutoffRow_bound hδ (hp q))

/-- All original stopping times are independent of the random-reference
parameter. Spatial regularization changes targets only. -/
theorem terminal_eq (p p' : Inputs) (ε ε' : ℝ≥0) (k : ℕ) (h : History Unit k) :
    (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p ε k).terminal h=
      (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p' ε' k).terminal h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ClippedCovariance.clip (v:ℝ) ((level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p ε k).terminal h.1) h.2.1=
      ClippedCovariance.clip (v:ℝ) ((level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p' ε' k).terminal h.1) h.2.1
    rw [ih h.1]

theorem nodeTime_eq (p p' : Inputs) (ε ε' : ℝ≥0) (k : ℕ) (h : History Unit k×(ℝ×HeatCircle)) :
    (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p ε k).nodeTime h=
      (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p' ε' k).nodeTime h := by
  change ClippedCovariance.clip (v:ℝ) ((level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p ε k).terminal h.1) h.2.1=
    ClippedCovariance.clip (v:ℝ) ((level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p' ε' k).terminal h.1) h.2.1
  rw [terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε ε' k h.1]

theorem observations_eq (p p' : Inputs) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) :
    (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p ε k).observations.observations h=
      (level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p' ε k).observations.observations h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg (fun t : ℝ => (⟨t,t+(ε:ℝ),h.2.2⟩ : Observation))
        (nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε ε k h)
    · exact congrFun (ih h.1) j

end SHE.ControlledReferenceRecursiveBounds
