module

public import SHE.HilbertColumns
public import SHE.HaarSingleHeat
public import SHE.HaarMeasurable
public import SHE.PredictableClock
public import SHE.CoefficientFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarHeatIntegrand
open MeasureTheory Set AddCircle CircleHeat FiniteHaar
open scoped ENNReal NNReal Topology
local instance haarHeatIntegrand_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance haarHeatIntegrand_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarHeatIntegrand_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance haarHeatIntegrand_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

abbrev Columns := HilbertColumns.Space HaarNode CircleL2
local instance haarHeatIntegrand_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarHeatIntegrand_columnsBorel : BorelSpace Columns := ⟨rfl⟩

/-- The literal square-summable Haar columns after positive heat time.
At nonpositive time the causal integrand is zero. -/
def kernel (ell M : ℝ) (hell : 0 < ell) (p : ℝ × EllipticField ell M) : Columns :=
  if ht : 0 < p.1 then
    HilbertColumns.ofSummable (fun q => heat p.1 (globalHaarColumn q p.2.1))
      (global_single_heat ht p.2.1 ell M hell p.2.2.1 p.2.2.2).1
  else 0

theorem kernel_apply (ell M : ℝ) (hell : 0 < ell) (p : ℝ × EllipticField ell M) (q : HaarNode) :
    kernel ell M hell p q=if 0 < p.1 then heat p.1 (globalHaarColumn q p.2.1) else 0 := by
  unfold kernel
  split_ifs <;> rfl

theorem kernel_measurable (ell M : ℝ) (hell : 0 < ell) : Measurable (kernel ell M hell) := by
  classical
  apply HilbertColumns.measurable_of_columns
  intro q
  have hm : Measurable (fun p : ℝ × EllipticField ell M => heat p.1 (globalHaarColumn q p.2.1)) :=
    (continuous_heat_action.comp (continuous_fst.prodMk
      ((continuous_fieldColumn ell M hell q).comp continuous_snd))).measurable
  have hi : Measurable (fun p : ℝ × EllipticField ell M =>
      if 0 < p.1 then heat p.1 (globalHaarColumn q p.2.1) else (0:CircleL2)) :=
    hm.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
  simpa only [kernel_apply] using hi

theorem kernel_norm_sq {ell M t : ℝ} (hell : 0 < ell) (ht : 0 < t) (f : EllipticField ell M) :
    ‖kernel ell M hell (t,f)‖^2=∑' q,‖heat t (globalHaarColumn q f.1)‖^2 := by
  rw [HilbertColumns.norm_sq]
  apply tsum_congr
  intro q
  rw [kernel_apply,ite_eq_left ht]

theorem kernel_norm_sq_bound {ell M t : ℝ} (hell : 0 < ell) (ht : 0 < t) (f : EllipticField ell M) :
    ‖kernel ell M hell (t,f)‖^2 ≤
      M*(1+2*HeatTrace.fractionalGaussianIntegral 0*t^(-(1/2:ℝ))) := by
  rw [kernel_norm_sq hell ht]
  exact (global_single_heat ht f.1 ell M hell f.2.1 f.2.2).2

theorem kernel_difference_norm_sq {ell M t : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (f g : EllipticField ell M) :
    ‖kernel ell M hell (t,f)-kernel ell M hell (t,g)‖^2=
      ∑' q,‖heat t (globalSignedColumn q f.1 g.1)‖^2 := by
  rw [HilbertColumns.norm_sq]
  apply tsum_congr
  intro q
  change ‖kernel ell M hell (t,f) q-kernel ell M hell (t,g) q‖^2=_
  simp only [kernel_apply,ite_eq_left ht]
  rw [← map_sub]
  rfl

/-- A predictable elliptic coefficient field gives an actual predictable
Hilbert-valued stochastic integrand for every terminal time. -/
theorem kernel_predictable {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) {ell M : ℝ} (hell : 0 < ell)
    (f : ℝ≥0 → Ω → EllipticField ell M) (hf : IsStronglyPredictable 𝓕 f) (t : ℝ) :
    IsStronglyPredictable 𝓕 (fun s ω => kernel ell M hell (t-(s:ℝ),f s ω)) := by
  change StronglyMeasurable[𝓕.predictable] (fun p : ℝ≥0 × Ω => kernel ell M hell (t-(p.1:ℝ),f p.1 p.2))
  exact ((kernel_measurable ell M hell).comp
    ((measurable_const.sub (PredictableClock.real_time_measurable 𝓕)).prodMk hf.measurable)).stronglyMeasurable

end SHE.HaarHeatIntegrand
