module

public import SHEStochastic.MatrixHeatWindowCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixStoppedHeatWindow
open MeasureTheory Set SHE SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.Elementwise
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (Q : Fin k → ℝ → Profile d)
    (hQ : ∀ i, Measurable (fun p : ℝ × AddCircle (1 : ℝ) => (Q i p.1).value p.2))
    (σ T : Fin k → ℝ) (x : Fin k → HeatCircle) (color : Fin k → d)
    (U : ℝ) (hUpper : ∀ i t, (Q i t).upper ≤ U)

/-- Original stop and target are independent pieces of history data. -/
def age (i : Fin k) (r : ℝ) : ℝ := if r < σ i then T i-r else 0

theorem age_measurable (i : Fin k) : Measurable (age σ T i) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.sub measurable_id) measurable_const

def row (i : Fin k) (r : ℝ) : Input (d := d) :=
  MatrixPointHeatRows.row (age σ T i r) (Q i r) (x i) (color i)

include hQ in
theorem row_measurable (i : Fin k) : Measurable (row Q σ T x color i) :=
  MatrixPointHeatRows.measurable _ (age_measurable σ T i) (fun _ => x i) measurable_const (Q i) (hQ i) (color i)

theorem row_zero (i : Fin k) {r : ℝ} (hr : σ i ≤ r) : row Q σ T x color i r=0 := by
  simp only [row,age,if_neg (not_lt.mpr hr),MatrixPointHeatRows.row,lt_self_iff_false,if_false]

/-- The original target age and the exact inactive-row mask are retained. -/
theorem row_target_bound (P : Profile d) {U : ℝ} (hP : P.upper ≤ U)
    (σ T : Fin k → ℝ) (x : Fin k → HeatCircle) (color : Fin k → d)
    (r : ℝ) (i : Fin k) (hages : σ i ≤ T i) :
    ‖row (fun _ _ => P) σ T x color i r‖ ≤
      Real.sqrt (if r < σ i then U*(1+heatConstant*(T i-r)^(-(1/2 : ℝ))) else 0) := by
  by_cases hi : r < σ i
  · have hb := MatrixPointHeatWindow.norm_sq P hP (le_refl (T i)) (hi.trans_le hages) (x i) (color i)
    rw [if_pos hi]
    change ‖MatrixPointHeatRows.row (age σ T i r) P (x i) (color i)‖ ≤ _
    rw [age,if_pos hi]
    exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hb)).mpr hb
  · rw [row_zero _ σ T x color i (not_lt.mp hi),norm_zero,if_neg hi,Real.sqrt_zero]

include hUpper in
theorem row_bound (hages : ∀ i, σ i ≤ T i) {a b : ℝ}
    (hstop : ∀ i, σ i ≤ a ∨ b ≤ σ i) (i : Fin k) {r : ℝ} (hr : r ∈ Ioo a b) :
    ‖row Q σ T x color i r‖^2 ≤ U*(1+heatConstant*(b-r)^(-(1/2 : ℝ))) := by
  rcases hstop i with hinactive | hactive
  · rw [row_zero Q σ T x color i (hinactive.trans hr.1.le),norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg ((Q i r).upper_pos.le.trans (hUpper i r))
      (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (sub_pos.mpr hr.2).le _)))
  · have hσ : r < σ i := hr.2.trans_le hactive
    change ‖MatrixPointHeatRows.row (age σ T i r) (Q i r) (x i) (color i)‖^2 ≤ _
    rw [age,if_pos hσ]
    exact MatrixPointHeatWindow.norm_sq (Q i r) (hUpper i r) (hactive.trans (hages i)) hr.2 (x i) (color i)

include hQ hUpper in
theorem row_integrable (hages : ∀ i, σ i ≤ T i) {a b : ℝ} (hab : a ≤ b)
    (hstop : ∀ i, σ i ≤ a ∨ b ≤ σ i) (i : Fin k) :
    IntervalIntegrable (fun r => ‖row Q σ T x color i r‖^2) volume a b :=
  GaussianHeatRowWindow.square_integrable _ (row_measurable Q hQ σ T x color i) hab
    (fun r hr => row_bound Q σ T x color U hUpper hages hstop i hr)

include hQ hUpper in
/-- Full history integrability also allows stop times inside the window.
Old-gap compatibility is needed for sharp gap estimates, not for defining
the actual covariance of the complete stopped history. -/
theorem row_integrable_all (hages : ∀ i, σ i ≤ T i) (a b : ℝ) (i : Fin k) :
    IntervalIntegrable (fun r => ‖row Q σ T x color i r‖^2) volume a b := by
  have hi : IntervalIntegrable (fun r : ℝ => r^(-(1/2 : ℝ))) volume (σ i-b) (σ i-a) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hj : IntervalIntegrable (fun r : ℝ => (σ i-r)^(-(1/2 : ℝ))) volume a b := by
    convert! (hi.comp_sub_left (σ i)).symm using 1 <;> ring
  have hp : IntervalIntegrable (fun r : ℝ => U*(1+heatConstant*(σ i-r)^(-(1/2 : ℝ)))) volume a b :=
    (intervalIntegrable_const.add (hj.const_mul heatConstant)).const_mul U
  apply hp.norm.mono_fun'
  · exact ((row_measurable Q hQ σ T x color i).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with r
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hr : r < σ i
    · change ‖MatrixPointHeatRows.row (age σ T i r) (Q i r) (x i) (color i)‖^2 ≤ _
      rw [age,if_pos hr]
      exact (MatrixPointHeatWindow.norm_sq (Q i r) (hUpper i r) (hages i) hr (x i) (color i)).trans (le_abs_self _)
    · rw [row_zero Q σ T x color i (not_lt.mp hr),norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact norm_nonneg _

def density_all (hages : ∀ i, σ i ≤ T i) (a b : ℝ) (hab : a ≤ b) : GaussianMatrixGramCurve.Density k :=
  GaussianRowGramCurve.density (row Q σ T x color) (row_measurable Q hQ σ T x color) a b hab
    (row_integrable_all Q hQ σ T x color U hUpper hages a b)

def covariance_all (hages : ∀ i, σ i ≤ T i) (a b : ℝ) (hab : a ≤ b) : GaussianContinuity.PositiveCovariance k :=
  GaussianMatrixGramCurve.path (density_all Q hQ σ T x color U hUpper hages a b hab) a

theorem covariance_all_entry (hages : ∀ i, σ i ≤ T i) (a b : ℝ) (hab : a ≤ b) (i j : Fin k) :
    (covariance_all Q hQ σ T x color U hUpper hages a b hab).val i j =
      ∫ r in a..b, inner ℝ (row Q σ T x color i r) (row Q σ T x color j r) := by
  change (GaussianMatrixGramCurve.path (density_all Q hQ σ T x color U hUpper hages a b hab) a).val i j = _
  rw [GaussianMatrixGramCurve.path_eq _ (show a ∈ Icc a b from ⟨le_rfl,hab⟩)]
  rfl

theorem covariance_all_add (hages : ∀ i, σ i ≤ T i) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    (covariance_all Q hQ σ T x color U hUpper hages a c (hab.trans hbc)).val =
      (covariance_all Q hQ σ T x color U hUpper hages a b hab).val+
      (covariance_all Q hQ σ T x color U hUpper hages b c hbc).val := by
  ext i j
  simp only [Matrix.add_apply,covariance_all_entry]
  have h1 : IntervalIntegrable (fun r => inner ℝ (row Q σ T x color i r) (row Q σ T x color j r)) volume a b :=
    (density_all Q hQ σ T x color U hUpper hages a b hab).integrable i j
  have h2 : IntervalIntegrable (fun r => inner ℝ (row Q σ T x color i r) (row Q σ T x color j r)) volume b c :=
    (density_all Q hQ σ T x color U hUpper hages b c hbc).integrable i j
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

/-- Removing an actual old interval leaves a positive residual
covariance, with all original stop masks and targets unchanged. -/
theorem residual_positive (hages : ∀ i, σ i ≤ T i) (a b c e : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) :
    ((covariance_all Q hQ σ T x color U hUpper hages a e (hab.trans (hbc.trans hce))).val-
      (covariance_all Q hQ σ T x color U hUpper hages b c hbc).val).PosSemidef := by
  rw [covariance_all_add Q hQ σ T x color U hUpper hages a b e hab (hbc.trans hce),
    covariance_all_add Q hQ σ T x color U hUpper hages b c e hbc hce]
  have he : (covariance_all Q hQ σ T x color U hUpper hages a b hab).val+
      ((covariance_all Q hQ σ T x color U hUpper hages b c hbc).val+
        (covariance_all Q hQ σ T x color U hUpper hages c e hce).val)-
      (covariance_all Q hQ σ T x color U hUpper hages b c hbc).val =
      (covariance_all Q hQ σ T x color U hUpper hages a b hab).val+
        (covariance_all Q hQ σ T x color U hUpper hages c e hce).val := by abel
  rw [he]
  exact (covariance_all Q hQ σ T x color U hUpper hages a b hab).property.add
    (covariance_all Q hQ σ T x color U hUpper hages c e hce).property

theorem covariance_all_inactive (hages : ∀ i, σ i ≤ T i) (a b : ℝ) (hab : a ≤ b)
    (i : Fin k) (hσ : σ i ≤ a) (j : Fin k) :
    (covariance_all Q hQ σ T x color U hUpper hages a b hab).val i j=0 := by
  rw [covariance_all_entry]
  apply intervalIntegral.integral_zero_ae
  filter_upwards with r hr
  rw [uIoc_of_le hab] at hr
  rw [row_zero Q σ T x color i (hσ.trans hr.1.le),inner_zero_left]

/-- An old Gaussian fraction has zero coordinates at observations that
have already stopped. This is a consequence of its actual covariance. -/
theorem gaussian_inactive (hages : ∀ i, σ i ≤ T i) (a b : ℝ) (hab : a ≤ b)
    (i : Fin k) (hσ : σ i ≤ a) :
    ∀ᵐ y ∂ProbabilityTheory.multivariateGaussian 0
      (covariance_all Q hQ σ T x color U hUpper hages a b hab).val, y i=0 :=
  OldIntervalCovariance.gaussian_coordinate_zero
    (covariance_all Q hQ σ T x color U hUpper hages a b hab).property i
    (covariance_all_inactive Q hQ σ T x color U hUpper hages a b hab i hσ)

def density (hages : ∀ i, σ i ≤ T i) (a b : ℝ) (hab : a ≤ b)
    (hstop : ∀ i, σ i ≤ a ∨ b ≤ σ i) : GaussianMatrixGramCurve.Density k :=
  GaussianRowGramCurve.density (row Q σ T x color) (row_measurable Q hQ σ T x color) a b hab
    (row_integrable Q hQ σ T x color U hUpper hages hab hstop)

def covariance (hages : ∀ i, σ i ≤ T i) (a b : ℝ) (hab : a ≤ b)
    (hstop : ∀ i, σ i ≤ a ∨ b ≤ σ i) : GaussianContinuity.PositiveCovariance k :=
  GaussianMatrixGramCurve.path (density Q hQ σ T x color U hUpper hages a b hab hstop) a

/-- Every original stop mask is retained in the actual matrix Gram;
the old-interval variance cap remains uniform for active and inactive rows. -/
theorem diagonal_bound (hages : ∀ i, σ i ≤ T i) {a b : ℝ} (hab : a < b) (hspan : b-a ≤ 1) (hU : 0 ≤ U)
    (hstop : ∀ i, σ i ≤ a ∨ b ≤ σ i) (i : Fin k) :
    (covariance Q hQ σ T x color U hUpper hages a b hab.le hstop).val i i ≤
      ProfileVariance.upperConstant*U*(b-a)^(1/2 : ℝ) :=
  GaussianHeatRowWindow.diagonal_bound (row Q σ T x color) (row_measurable Q hQ σ T x color)
    hab hspan hU (row_integrable Q hQ σ T x color U hUpper hages hab.le hstop)
    (fun i r hr => row_bound Q σ T x color U hUpper hages hstop i hr) i

end SHEStochastic.MatrixStoppedHeatWindow
