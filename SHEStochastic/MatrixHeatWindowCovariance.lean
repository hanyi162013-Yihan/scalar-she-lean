module

public import SHEStochastic.GaussianHeatRowWindow
public import SHEStochastic.MatrixPointHeatWindow
public import SHE.GaussianCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixHeatWindowCovariance
open MeasureTheory ProbabilityTheory Set SHE SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.Elementwise
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (Q : Fin k → ℝ → Profile d)
    (hQ : ∀ i, Measurable (fun p : ℝ × AddCircle (1 : ℝ) => (Q i p.1).value p.2))
    (T : Fin k → ℝ) (x : Fin k → HeatCircle) (color : Fin k → d)
    (U : ℝ) (hUpper : ∀ i r, (Q i r).upper ≤ U)

/-- Profiles retain their original physical time argument. Cutting an
old interval below never restarts a profile or moves a heat target. -/
def row (i : Fin k) (r : ℝ) : Input (d := d) :=
  MatrixPointHeatRows.row (T i-r) (Q i r) (x i) (color i)

include hQ in
theorem row_measurable (i : Fin k) : Measurable (row Q T x color i) :=
  MatrixPointHeatRows.measurable (fun r => T i-r) (measurable_const.sub measurable_id)
    (fun _ => x i) measurable_const (Q i) (hQ i) (color i)

include hUpper in
theorem row_bound {a b : ℝ} (hT : ∀ i, b ≤ T i) (i : Fin k) {r : ℝ} (hr : r ∈ Ioo a b) :
    ‖row Q T x color i r‖^2 ≤ U*(1+heatConstant*(b-r)^(-(1/2 : ℝ))) :=
  MatrixPointHeatWindow.norm_sq (Q i r) (hUpper i r) (hT i) hr.2 (x i) (color i)

include hQ hUpper in
theorem row_integrable {a b : ℝ} (hab : a ≤ b) (hT : ∀ i, b ≤ T i) (i : Fin k) :
    IntervalIntegrable (fun r => ‖row Q T x color i r‖^2) volume a b :=
  GaussianHeatRowWindow.square_integrable _ (row_measurable Q hQ T x color i) hab
    (fun r hr => row_bound Q T x color U hUpper hT i hr)

def density (a b : ℝ) (hab : a ≤ b) (hT : ∀ i, b ≤ T i) : GaussianMatrixGramCurve.Density k :=
  GaussianRowGramCurve.density (row Q T x color) (row_measurable Q hQ T x color) a b hab
    (row_integrable Q hQ T x color U hUpper hab hT)

def covariance (a b : ℝ) (hab : a ≤ b) (hT : ∀ i, b ≤ T i) : GaussianContinuity.PositiveCovariance k :=
  GaussianMatrixGramCurve.path (density Q hQ T x color U hUpper a b hab hT) a

/-- Every original component has the actual old-interval variance cap,
also when different observations use different matrix profiles. -/
theorem diagonal_bound {a b : ℝ} (hab : a < b) (hspan : b-a ≤ 1) (hU : 0 ≤ U)
    (hT : ∀ i, b ≤ T i) (i : Fin k) :
    (covariance Q hQ T x color U hUpper a b hab.le hT).val i i ≤
      ProfileVariance.upperConstant*U*(b-a)^(1/2 : ℝ) :=
  GaussianHeatRowWindow.diagonal_bound (row Q T x color) (row_measurable Q hQ T x color)
    hab hspan hU (row_integrable Q hQ T x color U hUpper hab.le hT)
    (fun i r hr => row_bound Q T x color U hUpper hT i hr) i

theorem coordinate_variance_bound {a b : ℝ} (hab : a < b) (hspan : b-a ≤ 1) (hU : 0 ≤ U)
    (hT : ∀ i, b ≤ T i) (i : Fin k) :
    Var[EuclideanSpace.proj (𝕜 := ℝ) i;
      multivariateGaussian 0 (covariance Q hQ T x color U hUpper a b hab.le hT).val] ≤
      ProfileVariance.upperConstant*U*(b-a)^(1/2 : ℝ) := by
  have he : Var[EuclideanSpace.proj (𝕜 := ℝ) i;
      multivariateGaussian 0 (covariance Q hQ T x color U hUpper a b hab.le hT).val] =
      (covariance Q hQ T x color U hUpper a b hab.le hT).val i i :=
    variance_eval_multivariateGaussian (covariance Q hQ T x color U hUpper a b hab.le hT).property i
  rw [he]
  exact diagonal_bound Q hQ T x color U hUpper hab hspan hU hT i

end SHEStochastic.MatrixHeatWindowCovariance
