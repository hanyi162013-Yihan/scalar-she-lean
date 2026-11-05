module

public import SHE.PastMeanTimeIntegral
public import SHE.BaselineUnitGain
public import SHE.BaselineCurrentTime
public import SHE.ObservationTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PastBaselineTime
open scoped ENNReal
open Set Filter MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain PastMeanTimeFactors
  QuarterRMSTimeFactors
local instance pastBaselineTime_period : Fact (0<2*π) := ⟨by positivity⟩
local instance pastBaselineTime_twoFinite : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
variable {R : ReferenceData} (L : Level R HeatCircle 1)

/-- The restored random-past baseline density has the SAME full-word
assignment budget, with only one fresh quarter-power singularity. -/
def restoredDensity (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (q A0 ν : ℝ) (p : History HeatCircle k) : ℝ :=
  BaselineOriginalGain.unitCoefficient P*totalIntegrand L P ell C k q (3/4:ℝ) A0 ν p

def budget (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (T v q A0 ν : ℝ) : ℝ :=
  BaselineOriginalGain.unitCoefficient P*oldTimeBudget P ell C k (T-v) (q-v) (3/4:ℝ) A0 ν

theorem old_time_bound (P : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ x,L.terminal x=T) {ell : ℝ} (hell : 0<ell)
    (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ)
    {q A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hA0 : 0≤A0) (hν : 0≤ν) :
    Integrable (fun t=>restoredDensity L P ell C k q A0 ν (QuarterSpatialEvent.anchor k t))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫ t,restoredDensity L P ell C k q A0 ν (QuarterSpatialEvent.anchor k t)
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      budget P ell C k T R.base q A0 ν := by
  have hh:=PastMeanTimeFactors.old_time_budget L P T hT hell C hC k hqbase hqT hTH
    (by norm_num : 0<(3/4:ℝ)) (by norm_num : (3/4:ℝ)≤1) hA0 hν
  refine ⟨hh.1.const_mul _,?_⟩
  simpa only [restoredDensity,budget,integral_const_mul] using
    mul_le_mul_of_nonneg_left hh.2 (BaselineOriginalGain.unitCoefficient_nonneg P)

/-- The relative-age baseline budget is genuinely current-time L2 for
every positive finite depth on the ORIGINAL absolute time interval. -/
theorem current_memLp (P : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (hk : 0<k) (v T A0 ν : ℝ) (hvT : v<T) (hν : 0<ν) :
    MemLp (fun q=>budget P ell C k T v q A0 ν) 2 (volume.restrict (Ioc v T)) := by
  have hm:=BaselineTimeLedger.baselineBudget_current_memLp P ell C k hk (T-v) A0 ν
    (sub_pos.mpr hvT) hν
  have hs : MeasurePreserving (fun q : ℝ=>q-v) (volume.restrict (Ioc v T))
      (volume.restrict (Ioc (0:ℝ) (T-v))) := by
    have ha:=(measurePreserving_add_right (volume:Measure ℝ) (-v)).restrict_preimage (s:=Ioc (0:ℝ) (T-v)) measurableSet_Ioc
    have he : (fun q : ℝ=>q+(-v))⁻¹' Ioc (0:ℝ) (T-v)=Ioc v T := by
      ext q
      simp only [mem_preimage,mem_Ioc]
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    rw [he] at ha
    simpa only [sub_eq_add_neg] using ha
  convert! (hm.comp_measurePreserving hs).const_mul (BaselineOriginalGain.unitCoefficient P) using 1

end SHE.PastBaselineTime
