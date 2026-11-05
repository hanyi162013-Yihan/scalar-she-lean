module

public import SHE.MarkedProfileTimeFactors
public import SHE.QuarterRMSOldTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.MarkedProfileTimeFactors
open Set MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalScoreChain PhysicalAssignmentGapScale ProfileL2 ControlledScoreRates
  PhysicalParentGeometry QuarterRMSTimeFactors QuarterSpatialEvent ScalarMeanEnvelope HistoryProductMeasure
open scoped BigOperators
open Classical
local instance profileInputOldTime_periodPos : Fact (0<2*π) := ⟨by positivity⟩
variable {R : ReferenceData} (L : Level R HeatCircle 1)

def gainDensity (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q A0 ν : ℝ) (p : History HeatCircle k) : ℝ :=
  if StrictHistory L k p ∧ q<(carrier L k).terminal p then
    (timeWeight L ell C k p*SharpWordTimeScale.total L P k p q A0 ν)*
      (sharpConstant P d*((((1+k:ℕ):ℝ)/(P.lower/2))*
        (((carrier L k).terminal p-q)/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1)))) else 0

theorem gainDensity_eq (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q A0 ν : ℝ) (p : History HeatCircle k) :
    gainDensity L P d ell C k q A0 ν p=
      inputConstant P d (1+k)*totalIntegrand L P ell C k q (freshDegree P) A0 ν p := by
  by_cases hp : StrictHistory L k p ∧ q<(carrier L k).terminal p
  · rw [gainDensity,ite_eq_left hp]
    exact active_density_identity L P d ell C k q A0 ν p hp.1 hp.2
  · simp only [gainDensity,totalIntegrand,hp,ite_false,mul_zero]

/-- Full old-time integration of the sharp actual-profile input scale,
under the original restricted product measure. The explicit assignment
budget retains all rough minimum gaps, full unassigned ages, root clips
and root masses. No old-time supremum or coarse spatial rate appears. -/
theorem gain_old_time_bound (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) {ell : ℝ} (hell : 0<ell)
    (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ)
    {q A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hA0 : 0≤A0) (hν : 0≤ν) :
    Integrable (fun t=>gainDensity L P d ell C k q A0 ν (anchor k t))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫ t,gainDensity L P d ell C k q A0 ν (anchor k t)
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
        inputConstant P d (1+k)*oldTimeBudget P ell C k T q (freshDegree P) A0 ν := by
  have hh := total_old_time_budget L P T hT hell C hC k hqbase hqT hTH
    (freshDegree_pos P) (freshDegree_le_one P) hA0 hν
  simp_rw [gainDensity_eq]
  refine ⟨hh.1.const_mul _,?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hh.2 (inputConstant_nonneg P d (1+k))

end SHE.MarkedProfileTimeFactors
