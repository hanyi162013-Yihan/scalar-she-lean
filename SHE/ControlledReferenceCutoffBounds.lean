module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.UncutSmoothWords
public import SHE.UncutHistoryMass
public import SHE.ControlledReferenceUncutBounds
public import SHE.CutoffWeightedDerivatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceCutoffBounds
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceCutoffBounds_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceCutoffBounds_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceCutoffBounds_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
local notation "Base" => ControlledReferenceLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF

/-- One genuine uncut heat-history majorant controls all actual
δ-dependent word values, uniformly over both random-reference inputs. -/
theorem test_norm_bound (k : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) (δ : ℝ) (hδ : 0<δ) h z,
    ‖(RecursiveHeatBounds.level (Base p) δ hδ 0 k).test h z‖≤C*UncutSmoothWords.weight (Base (0,0)) k h := by
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceUncutBounds.test_norm_bound P A hA Λ θ v b hvb Z htarget hstop F hF k
  refine ⟨C,hCn,fun p δ hδ h z => ?_⟩
  rw [CutoffUncutComparison.test_eq_active (Base p) hδ k h]
  by_cases hp : CutoffUncutComparison.Active (Base p) δ k h
  · simpa only [hp,ite_true] using hC p h z
  · simp only [hp,ite_false,Pi.zero_apply,norm_zero]
    exact mul_nonneg hCn (UncutSmoothWords.weight_nonneg (Base (0,0)) k h)

/-- The first derivatives of the ACTUAL moving cutoff words admit a
bound independent of δ and both reference inputs. Smooth coefficient
and finite-depth dependence remain in the explicit constant. -/
theorem fderiv_bound (k : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) (δ : ℝ) (hδ : 0<δ) h z,
    ‖fderiv ℝ ((RecursiveHeatBounds.level (Base p) δ hδ 0 k).test h) z‖≤C*UncutSmoothWords.weight (Base (0,0)) k h := by
  obtain ⟨C,hCn,hC⟩ := (ControlledReferenceUncutBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF k).fderiv.norm_bound
  refine ⟨C,hCn,fun p δ hδ h z => ?_⟩
  rw [CutoffUncutComparison.test_eq_active (Base p) hδ k h]
  by_cases hp : CutoffUncutComparison.Active (Base p) δ k h
  · rw [if_pos hp,UncutSmoothWords.test_eq_weight_normalized,fderiv_const_smul_field]
    simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base p) k h)]
    rw [ControlledReferenceUncutBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF p (0,0) k h]
    nlinarith [hC (p,h) z,UncutSmoothWords.weight_nonneg (Base (0,0)) k h]
  · rw [if_neg hp,fderiv_zero]
    simp only [Pi.zero_apply,norm_zero]
    exact mul_nonneg hCn (UncutSmoothWords.weight_nonneg (Base (0,0)) k h)

/-- The Hessians of the genuinely δ-dependent recursive words have the
same integrable majorant, uniformly over δ and the random past states. -/
theorem hessian_bound (k : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) (δ : ℝ) (hδ : 0<δ) h z,
    ‖GaussianTaylor.hessian ((RecursiveHeatBounds.level (Base p) δ hδ 0 k).test h) z‖≤C*UncutSmoothWords.weight (Base (0,0)) k h := by
  obtain ⟨C,hCn,hC⟩ := (ControlledReferenceUncutBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF k).fderiv.fderiv.norm_bound
  refine ⟨C,hCn,fun p δ hδ h z => ?_⟩
  rw [CutoffUncutComparison.test_eq_active (Base p) hδ k h]
  by_cases hp : CutoffUncutComparison.Active (Base p) δ k h
  · rw [if_pos hp,UncutSmoothWords.test_eq_weight_normalized]
    have hh := CutoffWeightedDerivatives.norm_hessian_smul_le (UncutSmoothWords.weight (Base p) k h) (UncutSmoothWords.normalized (Base p) k h) z
    rw [abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base p) k h)] at hh
    have hb : ‖GaussianTaylor.hessian (UncutSmoothWords.normalized (Base p) k h) z‖≤C := hC (p,h) z
    have he := hh.trans (mul_le_mul_of_nonneg_left hb (UncutSmoothWords.weight_nonneg (Base p) k h))
    rw [ControlledReferenceUncutBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF p (0,0) k h] at he
    rw [ControlledReferenceUncutBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF p (0,0) k h]
    exact he.trans_eq (mul_comm _ _)
  · rw [if_neg hp]
    have hh := CutoffWeightedDerivatives.norm_hessian_smul_le 0 (UncutSmoothWords.normalized (Base p) k h) z
    simp only [zero_smul,abs_zero,zero_mul] at hh
    exact hh.trans (mul_nonneg hCn (UncutSmoothWords.weight_nonneg (Base (0,0)) k h))

end SHE.ControlledReferenceCutoffBounds
