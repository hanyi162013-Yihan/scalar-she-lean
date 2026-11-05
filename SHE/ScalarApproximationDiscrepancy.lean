module

public import SHE.SmoothReferenceLimit
public import SHE.CoefficientFields
public import SHE.NativeSignedHaarProcess

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ScalarApproximationDiscrepancy
open MeasureTheory AddCircle SmoothApproximation ScalarData
open scoped Topology ENNReal
local instance scalarApproximationDiscrepancy_unitPositive : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
local instance scalarApproximationDiscrepancy_twoFinite : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance scalarApproximationDiscrepancy_realSigma : MeasurableSpace DyadicApproximation.RealL2 := borel _
local instance scalarApproximationDiscrepancy_realBorel : BorelSpace DyadicApproximation.RealL2 := ⟨rfl⟩
local instance scalarApproximationDiscrepancy_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance scalarApproximationDiscrepancy_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

variable (D : ScalarData)

def scalarError (n : ℕ) : ℝ := D.holderConstant * CompactMollifier.radius n ^ D.beta

theorem scalarError_nonneg (n : ℕ) : 0 ≤ scalarError D n :=
  mul_nonneg D.holderConstant_nonneg (Real.rpow_nonneg (CompactMollifier.radius_pos n).le _)

theorem coefficient_error (n : ℕ) (x : ℝ) :
    |D.residualCoefficient x - D.smoothCoefficient n x| ≤ scalarError D n := by
  simpa only [scalarError,ScalarData.smoothCoefficient,abs_sub_comm] using
    CompactMollifier.approximant_error D.residual_continuous D.holderConstant_nonneg
      D.beta_pos.le D.residual_holder n x

/-- The literal original squared coefficient difference is approximated
at both actual states. The common additive variance cancels exactly. -/
theorem original_difference_error (n : ℕ) (x y : ℝ) :
    |((D.coefficient x)^2-(D.coefficient y)^2)-
      (D.smoothCoefficient n x-D.smoothCoefficient n y)| ≤ SmoothReferenceLimit.error D n := by
  have hx := coefficient_error D n x
  have hy := coefficient_error D n y
  have hid : ((D.coefficient x)^2-(D.coefficient y)^2)-
      (D.smoothCoefficient n x-D.smoothCoefficient n y)=
      (D.residualCoefficient x-D.smoothCoefficient n x)-
      (D.residualCoefficient y-D.smoothCoefficient n y) := by
    rw [←D.variance_split x,←D.variance_split y]
    ring
  rw [hid]
  calc
    _ ≤ |D.residualCoefficient x-D.smoothCoefficient n x|+
        |D.residualCoefficient y-D.smoothCoefficient n y| := abs_sub _ _
    _ ≤ scalarError D n+scalarError D n := add_le_add hx hy
    _ = SmoothReferenceLimit.error D n := by simp only [scalarError,SmoothReferenceLimit.error]; ring

theorem smooth_abs_bound (n : ℕ) (x : ℝ) : |D.smoothCoefficient n x| ≤ D.cap := by
  rw [abs_of_nonneg (D.ell_pos.le.trans (D.smooth_bounds n x).1)]
  exact (D.smooth_bounds n x).2

def roughField (U : DyadicApproximation.RealL2) : CircleHeat.CircleL2 :=
  CoefficientFields.coefficient D.residualCoefficient D.residual_continuous.measurable
    D.cap D.residual_abs_bound U

def smoothField (n : ℕ) (U : DyadicApproximation.RealL2) : CircleHeat.CircleL2 :=
  CoefficientFields.coefficient (D.smoothCoefficient n)
    (D.smooth_boundedSmooth n).smooth.continuous.measurable D.cap (smooth_abs_bound D n) U

theorem roughField_measurable : Measurable (roughField D) :=
  CoefficientFields.measurable_coefficient D.beta_pos D.holderConstant_nonneg
    D.residualCoefficient D.residual_continuous.measurable D.residual_abs_bound D.residual_holder

theorem smoothField_measurable (n : ℕ) : Measurable (smoothField D n) :=
  CoefficientFields.measurable_coefficient D.beta_pos D.holderConstant_nonneg
    (D.smoothCoefficient n) (D.smooth_boundedSmooth n).smooth.continuous.measurable
    (smooth_abs_bound D n) (D.smooth_holder n)

theorem field_error (n : ℕ) (U : DyadicApproximation.RealL2) :
    ‖roughField D U-smoothField D n U‖ ≤ scalarError D n :=
  CoefficientFields.coefficient_uniform_error D.residualCoefficient (D.smoothCoefficient n)
    D.residual_continuous.measurable (D.smooth_boundedSmooth n).smooth.continuous.measurable
    D.cap D.cap D.residual_abs_bound (smooth_abs_bound D n) U
    (scalarError_nonneg D n) (coefficient_error D n)

/-- Actual nonlinear L² fields at arbitrary states, rather than merely
a scalar approximation or an assumed recursive-word limit. -/
theorem difference_field_error (n : ℕ) (U V : DyadicApproximation.RealL2) :
    ‖(roughField D U-roughField D V)-(smoothField D n U-smoothField D n V)‖ ≤
      SmoothReferenceLimit.error D n := by
  have he : (roughField D U-roughField D V)-(smoothField D n U-smoothField D n V)=
      (roughField D U-smoothField D n U)-(roughField D V-smoothField D n V) := by abel
  rw [he]
  calc
    _ ≤ ‖roughField D U-smoothField D n U‖+‖roughField D V-smoothField D n V‖ := norm_sub_le _ _
    _ ≤ scalarError D n+scalarError D n := add_le_add (field_error D n U) (field_error D n V)
    _ = SmoothReferenceLimit.error D n := by simp only [scalarError,SmoothReferenceLimit.error]; ring

def differenceError (n : ℕ) (U V : DyadicApproximation.RealL2) : CircleHeat.CircleL2 :=
  (roughField D U-roughField D V)-(smoothField D n U-smoothField D n V)

theorem differenceError_measurable {X : Type*} [MeasurableSpace X]
    (n : ℕ) (U V : X→DyadicApproximation.RealL2) (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun x=>differenceError D n (U x) (V x)) :=
  (((roughField_measurable D).comp hU).sub ((roughField_measurable D).comp hV)).sub
    (((smoothField_measurable D n).comp hU).sub ((smoothField_measurable D n).comp hV))

/-- This includes dependent random states and arbitrary finite time/sample
measures. There is no independence or exceptional-set substitution. -/
theorem differenceError_energy {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (n : ℕ)
    (U V : X→DyadicApproximation.RealL2) (hU : Measurable U) (hV : Measurable V) :
    Integrable (fun x=>‖differenceError D n (U x) (V x)‖^2) ν ∧
      (∫x,‖differenceError D n (U x) (V x)‖^2 ∂ν)≤
        SmoothReferenceLimit.error D n^2*(ν Set.univ).toReal := by
  have hm := (differenceError_measurable D n U V hU hV).norm.pow_const (2:ℕ)
  have hb (x : X) : ‖differenceError D n (U x) (V x)‖^2≤SmoothReferenceLimit.error D n^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (difference_field_error D n (U x) (V x)) 2
  have hi : Integrable (fun x=>‖differenceError D n (U x) (V x)‖^2) ν :=
    (integrable_const (SmoothReferenceLimit.error D n^2)).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hb x))
  refine ⟨hi,?_⟩
  calc
    _≤∫_x: X,SmoothReferenceLimit.error D n^2 ∂ν :=
      integral_mono hi (integrable_const _) hb
    _=SmoothReferenceLimit.error D n^2*(ν Set.univ).toReal := by
      rw [integral_const]
      change (ν Set.univ).toReal * _ = _
      ring

end SHE.ScalarApproximationDiscrepancy
