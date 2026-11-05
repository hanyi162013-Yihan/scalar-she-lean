module

public import SHE.ShiftedOldTimeMeasure
public import SHE.ShiftedPhysicalArrays

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.ShiftedIntervalCovariance
open Set MeasureTheory StoppedFourier WordRecursion PhysicalScoreChain OldIntervalCovariance
  StoppedGaussianFeatures ObservationTimeShift
local instance shiftedIntervalCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {N : ℕ}

theorem interval_measure_translation (v lo hi : ℝ) : MeasurePreserving (translation v)
    (intervalMeasure lo hi) (intervalMeasure (lo+v) (hi+v)) := by
  have ht := (measurePreserving_add_right (volume : Measure ℝ) v).restrict_preimage
    (measurableSet_Ioc : MeasurableSet (Ioc (lo+v) (hi+v)))
  have he : (fun t : ℝ=>t+v) ⁻¹' Ioc (lo+v) (hi+v)=Ioc lo hi := by
    ext t
    simp only [mem_preimage,mem_Ioc,add_lt_add_iff_right,add_le_add_iff_right]
  rw [he] at ht
  exact ht.prod (MeasurePreserving.id (AddCircle.haarAddCircle (T:=2*Real.pi)))

/-- The original stopped covariance restricted to an interval after
time zero is its literal interval integral, with no positivity premise. -/
theorem intervalCovariance_eq_integral (Z : Fin N→Observation) (c : Domain→ℝ)
    (lo hi : ℝ) (hlo : 0≤lo) (i j : Fin N) :
    intervalCovariance Z c lo hi i j=
      ∫ p,c p*stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) p i*
        stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) p j
        ∂intervalMeasure lo hi := by
  unfold intervalCovariance StoppedGaussianFeatures.stoppedCovariance
  have he : (fun p=>intervalProfile c lo hi p*
      stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) p i*
      stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) p j)=
      (timeSet lo hi).indicator (fun p=>c p*
      stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) p i*
      stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) p j) := by
    funext p
    by_cases hp : p∈timeSet lo hi
    · simp only [intervalProfile,indicator_of_mem hp]
    · simp only [intervalProfile,indicator_of_notMem hp,zero_mul]
  have hI : MeasurableSet (timeSet lo hi):=measurableSet_Ioc.prod MeasurableSet.univ
  rw [he,integral_indicator hI,←intervalMeasure_eq_restrict hlo]

/-- Exact covariance transport for the genuine old interval. The
nonnegative lower endpoints discharge the time-zero cutoff on both sides. -/
theorem intervalCovariance_translation (v : ℝ) (Z : Fin N→Observation) (c : Domain→ℝ)
    (lo hi : ℝ) (hlo : 0≤lo) (hlov : 0≤lo+v) :
    intervalCovariance (observations v Z) (profile v c) (lo+v) (hi+v)=intervalCovariance Z c lo hi := by
  ext i j
  rw [intervalCovariance_eq_integral _ _ _ _ hlov,intervalCovariance_eq_integral _ _ _ _ hlo]
  rw [←(interval_measure_translation v lo hi).integral_comp']
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [observations_stop,observations_target,observations_center,profile_translation,
    stoppedRow_translation]

end SHE.ShiftedIntervalCovariance
