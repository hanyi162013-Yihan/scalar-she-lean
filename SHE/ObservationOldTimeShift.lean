module

public import SHE.ObservationTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ObservationOldTimeShift
open Set MeasureTheory ProbabilityTheory AddCircle WordRecursion StoppedFourier
  StoppedGaussianFeatures OldIntervalCovariance ObservationTimeShift
open scoped Topology BigOperators
local instance observationOldTimeShift_period : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r : ℕ}

/-- Once an old interval lies after the history's lower cutoff, its
physical measure does not depend on that cutoff. -/
theorem history_interval_measure (q lo hi : ℝ) (hql : q≤lo) :
    (historyMeasure q).restrict (timeSet lo hi)=intervalMeasure lo hi := by
  unfold historyMeasure timeSet intervalMeasure
  rw [← Measure.restrict_prod_eq_prod_univ,Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  exact inter_eq_left.mpr (fun t ht => hql.trans ht.1.le)

theorem oldCovariance_interval_integral (q lo hi : ℝ) (hql : q≤lo)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (c : Domain → ℝ) :
    StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) q=
      fun i j => ∫ p,c p*stoppedRow σ target center p i*stoppedRow σ target center p j
        ∂intervalMeasure lo hi := by
  ext i j
  unfold StoppedGaussianFeatures.stoppedCovariance
  have he : (fun p => intervalProfile c lo hi p*stoppedRow σ target center p i*
      stoppedRow σ target center p j)=(timeSet lo hi).indicator
        (fun p => c p*stoppedRow σ target center p i*stoppedRow σ target center p j) := by
    funext p
    by_cases hp : p ∈ timeSet lo hi
    · simp only [intervalProfile,Set.indicator_of_mem hp]
    · simp only [intervalProfile,Set.indicator_of_notMem hp,zero_mul]
  have hs : MeasurableSet (timeSet lo hi) := measurableSet_Ioc.prod MeasurableSet.univ
  rw [he,integral_indicator hs,history_interval_measure q lo hi hql]

/-- The old-interval covariance has exactly the same value for any two
lower history cutoffs before that interval. No integrability premise is
needed for this measure identity. -/
theorem oldCovariance_base_eq (q q' lo hi : ℝ) (hql : q≤lo) (hq'l : q'≤lo)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (c : Domain → ℝ) :
    StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) q=
      StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) q' := by
  rw [oldCovariance_interval_integral q lo hi hql,
    oldCovariance_interval_integral q' lo hi hq'l]

/-- The actual old increment at absolute times lo+v,hi+v has precisely
the relative-time law. The conventional base zero in familyCovariance
is kept unchanged on both sides; old-interval support discharges it. -/
theorem familyCovariance_translation (v : ℝ) (hv : 0≤v)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (c : Domain → ℝ)
    (lo hi : Fin r → ℝ) (hlo : ∀ j,0≤lo j) (j : Fin r) :
    familyCovariance (fun i=>σ i+v) (fun i=>target i+v) center (profile v c)
      (fun j=>lo j+v) (fun j=>hi j+v) j=
      familyCovariance σ target center c lo hi j := by
  unfold familyCovariance
  rw [oldCovariance_base_eq 0 v (lo j+v) (hi j+v) (by linarith [hlo j])
    (by linarith [hlo j])]
  convert oldCovariance_translation v 0 (lo j) (hi j) σ target center c using 1; simp only [zero_add]

theorem familyDirection_translation (v : ℝ) (σ target : Fin n → ℝ)
    (center : Fin n → HeatCircle) (lo : Fin r → ℝ) (x : Fin r → HeatCircle) (j : Fin r) :
    familyDirection (fun i=>σ i+v) (fun i=>target i+v) center (fun j=>lo j+v) x j=
      familyDirection σ target center lo x j :=
  stoppedRow_translation v σ target center (lo j,x j)

/-- Equality of the literal independent old Gaussian product laws,
not merely a coordinatewise moment comparison. -/
theorem oldGaussianProduct_translation (v : ℝ) (hv : 0≤v)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (c : Domain → ℝ)
    (lo hi : Fin r → ℝ) (hlo : ∀ j,0≤lo j) :
    Measure.pi (fun j=>multivariateGaussian (0 : State n)
      (familyCovariance (fun i=>σ i+v) (fun i=>target i+v) center (profile v c)
        (fun j=>lo j+v) (fun j=>hi j+v) j))=
    Measure.pi (fun j=>multivariateGaussian (0 : State n)
      (familyCovariance σ target center c lo hi j)) := by
  congr 1
  funext j
  rw [familyCovariance_translation v hv σ target center c lo hi hlo j]

/-- Scalar damping and defect weights keep the ORIGINAL stopping time
under the same physical time translation. -/
theorem damping_translation (v Λ σ q : ℝ) :
    Real.exp (-Λ*((σ+v)-(q+v)))=Real.exp (-Λ*(σ-q)) := by
  rw [add_sub_add_right_eq_sub]

theorem gap_translation (v a b : ℝ) : (b+v)-(a+v)=b-a := by ring

theorem order_translation (v a b : ℝ) : a+v<b+v ↔ a<b := add_lt_add_iff_right v

theorem native_translation (v σ target : ℝ) : σ+v=target+v ↔ σ=target :=
  add_right_cancel_iff

end SHE.ObservationOldTimeShift
