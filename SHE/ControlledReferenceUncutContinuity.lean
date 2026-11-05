module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.UncutSmoothWords
public import SHE.UncutHistoryMass
public import SHE.ControlledReferenceUncutBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceUncutContinuity
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceUncutContinuity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceUncutContinuity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceUncutContinuity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
local notation "Base" => ControlledReferenceLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall in
/-- True normalized uncut words are jointly continuous in the two
past-state reference inputs and their finite-dimensional state. -/
theorem normalized_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History Unit k) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) => UncutSmoothWords.normalized (Base q.1) k h q.2) := by
  induction k with
  | zero => exact hF.smooth.continuous.comp continuous_snd
  | succ k ih =>
    let G := fun p : Inputs => UncutSmoothWords.normalized (Base p) k h.1
    have hG := ih h.1
    have hGs := uniform_reindex
      (ControlledReferenceUncutBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF k)
      (fun p : Inputs => (p,h.1))
    have hC := ControlledReferenceRecursiveContinuity.nodeCovariance_continuous P A hA Λ θ v b hvb Z htarget hstop F hF 1 zero_lt_one hsmall hΛ 0 k h
    have hH := GaussianParameterContinuity.continuous_average_hessian G hG hGs
      (fun p : Inputs => (CutoffCarriers.carrier (Base p) k).nodeCovariance h) hC
    have hp : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
        (q.1,SmoothWords.tailProjection (n+k) q.2)) :=
      continuous_fst.prodMk ((SmoothWords.tailProjection (n+k)).continuous.comp continuous_snd)
    have hH' := hH.comp hp
    have hr : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
        NormalizedInsertion.unitRow (CutoffCarriers.row (Base q.1) k h)) := by
      have he : (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
          NormalizedInsertion.unitRow (CutoffCarriers.row (Base q.1) k h))=
          fun _ => NormalizedInsertion.unitRow (CutoffCarriers.row (Base (0,0)) k h) := by
        funext q
        rw [ControlledReferenceUncutBounds.row_eq P A hA Λ θ v b hvb Z htarget hstop F hF q.1 (0,0) k h]
      rw [he]
      exact continuous_const
    have hd := (hH'.clm_apply hr).clm_apply hr
    have ha := hA.smooth.continuous.comp ((SmoothWords.headProjection (n+k)).continuous.comp
      (continuous_snd : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) => q.2)))
    have href : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
        ControlledReferenceWindows.coefficient P Λ θ v q.1 ((CutoffCarriers.carrier (Base q.1) k).nodeTime h,h.2.2)) := by
      have he : (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
          ControlledReferenceWindows.coefficient P Λ θ v q.1 ((CutoffCarriers.carrier (Base q.1) k).nodeTime h,h.2.2))=
          fun q => ControlledReferenceWindows.coefficient P Λ θ v q.1 ((CutoffCarriers.carrier (Base (0,0)) k).nodeTime h,h.2.2) := by
        funext q
        rw [ControlledReferenceUncutBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF q.1 (0,0) k h]
      rw [he]
      exact (ControlledReferenceWindows.coefficient_inputs_continuous P Λ θ v hΛ hsmall _).comp continuous_fst
    exact (continuous_const.mul (ha.sub href)).mul hd

include hsmall in
/-- The full uncut tests inherit actual parameter continuity. Their
possibly singular heat-history weight is independent of the reference
inputs and is kept explicit in the separate integrability theorem. -/
theorem test_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History Unit k) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) => UncutSmoothWords.test (Base q.1) k h q.2) := by
  have hh := (normalized_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hsmall hΛ k h).const_smul
    (UncutSmoothWords.weight (Base (0,0)) k h)
  convert hh using 1
  funext q
  rw [UncutSmoothWords.test_eq_weight_normalized,Pi.smul_apply,
    ControlledReferenceUncutBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF q.1 (0,0) k h]
  rfl

end SHE.ControlledReferenceUncutContinuity
