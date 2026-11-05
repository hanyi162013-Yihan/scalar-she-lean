module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRecursiveBackward
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceRecursiveBackward_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRecursiveBackward_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRecursiveBackward_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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
/-- Genuine continuity of the actual reserve covariance at any recursive
history and any backward time, uniformly allowing terminal covariance
zero and collisions. -/
theorem window_path_continuous (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ)
    (h : History Unit k) (t : ℝ) :
    Continuous (fun p : Inputs => ((L p ε k).window h).path t) := by
  apply Continuous.subtype_mk
  let T := (L (0,0) ε k).terminal h
  let Z₀ := (L (0,0) ε k).observations.observations h
  have hc := ControlledReferenceCovariance.covariance_inputs_continuous P hΛ θ v hsmall Z₀ T
    (ClippedCovariance.clip_mem ((L (0,0) ε k).terminal_base h) t).2
    ((L (0,0) ε k).targets_after h)
  convert hc using 1
  funext p
  change WordRecursion.covariance (ControlledReferenceWindows.coefficient P Λ θ v p)
    ((L p ε k).observations.observations h)
    (ClippedCovariance.clip (v:ℝ) ((L p ε k).terminal h) t) ((L p ε k).terminal h)=_
  rw [ControlledReferenceRecursiveBounds.observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε k h,
    ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h]
  rfl

include hsmall in
/-- The reserve Gaussian smoothing of the genuinely recursive test is
jointly continuous in the original past inputs and its current mean. -/
theorem continuous_backward (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (t : ℝ) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) =>
      GaussianItoTest.backward ((L q.1 ε k).window h) ((L q.1 ε k).test h) t q.2) := by
  obtain ⟨C,hCn,hC⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k).norm_bound
  exact GaussianParameterContinuity.continuous_average
    (fun p : Inputs => (L p ε k).test h)
    (ControlledReferenceRecursiveContinuity.continuous_test P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h)
    (fun p z => hC (p,(ε,h)) z)
    (fun p : Inputs => ((L p ε k).window h).path t)
    (window_path_continuous P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h t)

include hsmall in
/-- Actual full reserve Hessians of the moving recursive words are
jointly continuous in their original past inputs and current mean. -/
theorem continuous_hessian (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (t : ℝ) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) => GaussianTaylor.hessian
      (GaussianItoTest.backward ((L q.1 ε k).window h) ((L q.1 ε k).test h) t) q.2) := by
  have hFs := uniform_reindex
    (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k)
    (fun p : Inputs => (p,(ε,h)))
  exact GaussianParameterContinuity.continuous_average_hessian
    (fun p : Inputs => (L p ε k).test h)
    (ControlledReferenceRecursiveContinuity.continuous_test P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h)
    hFs (fun p : Inputs => ((L p ε k).window h).path t)
    (window_path_continuous P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h t)

end SHE.ControlledReferenceRecursiveBackward
