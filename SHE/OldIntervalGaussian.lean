module

public import SHE.OldIntervalRange
public import SHE.GaussianRangeSupport

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.OldIntervalCovariance
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianRangeSmooth
  GaussianAssignmentBlocks StoppedGaussianFeatures StoppedFourier
open scoped Topology BigOperators Matrix.Norms.L2Operator
local instance oldIntervalGaussian_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r k : ℕ}

theorem gaussian_coordinate_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (i : Fin n) (hrow : ∀ j, A i j = 0) :
    ∀ᵐ y : State n ∂multivariateGaussian 0 A, y i = 0 := by
  filter_upwards [ae_mem_own_covariance_range hA] with y hy
  obtain ⟨z, rfl⟩ := hy
  change (Matrix.toEuclideanLin A z) i = 0
  change ∑ j, A i j * z j = 0
  simp only [hrow, zero_mul, Finset.sum_const_zero]

/-- A genuine Gaussian old increment has zero later-leaf coordinates
almost surely, including singular covariance and collision cases. -/
theorem interval_gaussian_inactive (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    {M lo hi : ℝ} (hb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (i : Fin n) (hiStop : σ i ≤ lo) :
    ∀ᵐ y : State n ∂multivariateGaussian 0 (stoppedCovariance σ target center (intervalProfile c lo hi) 0),
      y i = 0 :=
  gaussian_coordinate_zero (covariance_posSemidef σ target center hages c hc hb lo hi) i
    (fun j => covariance_inactive_row σ target center c lo hi i j hiStop)

def familyCovariance (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (c : Domain → ℝ) (lo hi : Fin r → ℝ) (j : Fin r) : Matrix (Fin n) (Fin n) ℝ :=
  stoppedCovariance σ target center (intervalProfile c (lo j) (hi j)) 0

def familyDirection (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (lo : Fin r → ℝ) (x : Fin r → HeatCircle) (j : Fin r) : State n :=
  stoppedRow σ target center (lo j, x j)

theorem family_directions_mem_range_ae (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (lo hi : Fin r → ℝ) (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, σ i ≤ lo j ∨ hi j ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) {ell M : ℝ} (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ M) :
    ∀ᵐ x : Fin r → HeatCircle ∂Measure.pi (fun _ : Fin r => haarAddCircle), ∀ j,
      familyDirection σ target center lo x j ∈
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (familyCovariance σ target center c lo hi j)).range := by
  apply ae_all_iff.mpr
  intro j
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin r => haarAddCircle) j).ae
    (endpoint_row_mem_range_ae σ target center hσ hσ1 hages (hlo j) (hgap j) (hstop j) c hc hell hb)

/-- Every old interval and every original observation coordinate retain
their genuine triangular support under the actual independent Gaussian law. -/
theorem family_gaussian_inactive (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    {M : ℝ} (hb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (lo hi : Fin r → ℝ) :
    ∀ᵐ y : Fin r → State n ∂Measure.pi
      (fun j => multivariateGaussian 0 (familyCovariance σ target center c lo hi j)),
      ∀ j i, σ i ≤ lo j → y j i = 0 := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro i
  by_cases hs : σ i ≤ lo j
  · exact ((Measure.quasiMeasurePreserving_eval
      (fun j => multivariateGaussian (0 : State n) (familyCovariance σ target center c lo hi j)) j).ae
        (interval_gaussian_inactive σ target center hages c hc hb i hs)).mono (fun _ hy _ => hy)
  · exact ae_of_all _ (fun _ h => (hs h).elim)

/-- Exact centered block identity for the actual finite family of old
physical interval covariances and insertion directions. PSD and singular
range applicability are conclusions of the physical construction. -/
theorem actual_gaussian_assignment_ae (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (lo hi : Fin r → ℝ) (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, σ i ≤ lo j ∨ hi j ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) {ell M : ℝ} (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ M)
    (is : List (Fin r)) (hnd : is.Nodup)
    (F : (Fin r → HeatCircle) → Fin k → (Fin r → State n) → ℝ)
    (hF : ∀ x j, Measurable (F x j)) (B : (Fin r → HeatCircle) → ℝ)
    (hB : ∀ x y, |∏ j, F x j y| ≤ B x) :
    ∀ᵐ x : Fin r → HeatCircle ∂Measure.pi (fun _ : Fin r => haarAddCircle),
      let A := familyCovariance σ target center c lo hi
      let D := familyDirection σ target center lo x
      (∫ y, (∏ j, MeasurableGaussianScores.secondScore (A j) (D j) (y j)) * (∏ j, F x j y)
        ∂Measure.pi (fun j => multivariateGaussian 0 (A j))) =
        ∫ y, (∏ j, MeasurableGaussianScores.secondScore (A j) (D j) (y j)) *
          ((assignments (m := k) is).map (fun choices => assignmentWord choices (F x) y)).sum
          ∂Measure.pi (fun j => multivariateGaussian 0 (A j)) := by
  filter_upwards [family_directions_mem_range_ae σ target center hσ hσ1 hages lo hi hlo hgap hstop c hc hell hb]
    with x hx
  exact gaussian_product_identity _
    (fun j => covariance_posSemidef σ target center hages c hc
      (fun p => ⟨hell.le.trans (hb p).1, (hb p).2⟩) (lo j) (hi j)) _ hx is hnd (F x) (hF x) (B x) (hB x)

end SHE.OldIntervalCovariance
