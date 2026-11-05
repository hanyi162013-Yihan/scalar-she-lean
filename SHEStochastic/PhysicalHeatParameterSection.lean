module

public import SHEStochastic.HeatParameterPullback
public import SHEStochastic.L2ExtendedUniformNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.PhysicalHeatParameterSection
open MeasureTheory HeatParameterCover HeatParameterPullback SHE SHE.StoppedFourier AddCircle Filter
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem measurable_function (Y : C(Parameter, ℝ)) (t : ShortTime) :
    Measurable (fun a : HeatCircle ↦ Y (point t a)) :=
  Y.continuous.measurable.comp (measurable_point.comp (measurable_const.prodMk measurable_id))

theorem memLp (p : ℝ≥0∞) (Y : C(Parameter, ℝ)) (t : ShortTime) :
    MemLp (fun a : HeatCircle ↦ Y (point t a)) p haarAddCircle :=
  MemLp.of_bound (measurable_function Y t).aestronglyMeasurable ‖Y‖
    (Filter.Eventually.of_forall fun a ↦ Y.norm_coe_le_norm _)

/-- The physical spatial section as an actual Lp class. The same
construction at p=2 and p=infinity connects the original state topology
with the uniform-norm bound used in localization. -/
def value (p : ℝ≥0∞) (Y : C(Parameter, ℝ)) (t : ShortTime) :
    Lp ℝ p (haarAddCircle (T := 2 * Real.pi)) :=
  (memLp p Y t).toLp _

theorem value_ae (p : ℝ≥0∞) (Y : C(Parameter, ℝ)) (t : ShortTime) :
    value p Y t =ᵐ[haarAddCircle] fun a ↦ Y (point t a) := (memLp p Y t).coeFn_toLp

theorem difference_bound_profiles (p : ℝ≥0∞) [Fact (1 ≤ p)] (Y Z : C(Parameter, ℝ))
    (t s : ShortTime) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a : HeatCircle, |Y (point t a) - Z (point s a)| ≤ C) :
    ‖value p Y t - value p Z s‖ ≤ C := by
  have hh : ∀ᵐ a ∂haarAddCircle, ‖(value p Y t - value p Z s) a‖ ≤ C := by
    filter_upwards [value_ae p Y t, value_ae p Z s, Lp.coeFn_sub (value p Y t) (value p Z s)]
      with a ht hs he
    rw [he, Pi.sub_apply, ht, hs, Real.norm_eq_abs]
    exact hbound a
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.one_rpow,
    NNReal.coe_one, Real.one_rpow, one_mul] using Lp.norm_le_of_ae_bound hC hh

theorem difference_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (Y : C(Parameter, ℝ))
    (t s : ShortTime) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a : HeatCircle, |Y (point t a) - Y (point s a)| ≤ C) :
    ‖value p Y t - value p Y s‖ ≤ C := difference_bound_profiles p Y Y t s hC hbound

theorem lipschitz_profile (p : ℝ≥0∞) [Fact (1 ≤ p)] (t : ShortTime) :
    LipschitzWith 1 (fun Y : C(Parameter, ℝ) ↦ value p Y t) := by
  apply LipschitzWith.of_dist_le_mul
  intro Y Z
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact difference_bound_profiles p Y Z t t (norm_nonneg _) (fun a ↦ (Y - Z).norm_coe_le_norm _)

theorem uniformContinuous_value (p : ℝ≥0∞) [Fact (1 ≤ p)] (Y : C(Parameter, ℝ)) :
    UniformContinuous (value p Y) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := uniform_time_continuity Y Y.continuous (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun t s hts ↦ ?_⟩
  have hd : |t.val - s.val| < δ := hts
  rw [dist_eq_norm]
  exact (difference_bound p Y t s (by positivity : 0 ≤ ε / 2)
    (fun a ↦ (hh t s hd a).le)).trans_lt (by linarith)

theorem uniform_norm_bound (Y : C(Parameter, ℝ)) (t : ShortTime) :
    L2ExtendedUniformNorm.value haarAddCircle (value 2 Y t) ≤ ENNReal.ofReal ‖Y‖ := by
  apply (L2ExtendedUniformNorm.le_iff haarAddCircle _ _).mpr
  filter_upwards [value_ae 2 Y t] with a ha
  rw [ha, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (Y.norm_coe_le_norm _)

theorem value_initial (p : ℝ≥0∞) (Y : C(Parameter, ℝ))
    (hz : ∀ q, Y (HeatParameterCoordinates.zeroTime q) = 0) : value p Y initialTime = 0 := by
  apply Lp.ext
  filter_upwards [value_ae p Y initialTime, Lp.coeFn_zero ℝ p (haarAddCircle (T := 2 * Real.pi))]
    with a ha h0
  have hh := hz (point initialTime a)
  rw [zeroTime_point] at hh
  exact ha.trans (hh.trans h0.symm)

theorem initial_trace (p : ℝ≥0∞) [Fact (1 ≤ p)] (Y : C(Parameter, ℝ))
    (hz : ∀ q, Y (HeatParameterCoordinates.zeroTime q) = 0) :
    Tendsto (value p Y) (𝓝 initialTime) (𝓝 0) := by
  simpa only [value_initial p Y hz] using (uniformContinuous_value p Y).continuous.tendsto initialTime

/-- The Borel extended uniform norm of the L2 state is exactly the
norm of its L-infinity lift. In particular it varies continuously in
time for this physical convolution, without continuity of a chosen
spatial representative at the circle seam. -/
theorem uniform_norm_eq (Y : C(Parameter, ℝ)) (t : ShortTime) :
    L2ExtendedUniformNorm.value haarAddCircle (value 2 Y t) = ENNReal.ofReal ‖value ∞ Y t‖ := by
  have he : (value 2 Y t : HeatCircle → ℝ) =ᵐ[haarAddCircle] (value ∞ Y t : HeatCircle → ℝ) :=
    (value_ae 2 Y t).trans (value_ae ∞ Y t).symm
  change eLpNorm (value 2 Y t) ∞ haarAddCircle = _
  rw [eLpNorm_congr_ae he, ← Lp.enorm_def, ← ofReal_norm]

theorem continuous_uniform_norm (Y : C(Parameter, ℝ)) :
    Continuous (fun t ↦ L2ExtendedUniformNorm.value haarAddCircle (value 2 Y t)) := by
  simp_rw [uniform_norm_eq]
  exact ENNReal.continuous_ofReal.comp (uniformContinuous_value ∞ Y).continuous.norm

theorem real_uniform_norm_eq (Y : C(Parameter, ℝ)) (t : ShortTime) :
    L2ExtendedUniformNorm.realValue haarAddCircle (value 2 Y t) = ‖value ∞ Y t‖ := by
  rw [L2ExtendedUniformNorm.realValue, uniform_norm_eq, ENNReal.toReal_ofReal (norm_nonneg _)]

theorem continuous_real_uniform_norm (Y : C(Parameter, ℝ)) :
    Continuous (fun t ↦ L2ExtendedUniformNorm.realValue haarAddCircle (value 2 Y t)) := by
  simp_rw [real_uniform_norm_eq]
  exact (uniformContinuous_value ∞ Y).continuous.norm

def path (p : ℝ≥0∞) [Fact (1 ≤ p)] (Y : C(Parameter, ℝ)) :
    C(ShortTime, Lp ℝ p (haarAddCircle (T := 2 * Real.pi))) :=
  ⟨value p Y, (uniformContinuous_value p Y).continuous⟩

theorem lipschitz_path (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    LipschitzWith 1 (path p) := by
  apply LipschitzWith.of_dist_le_mul
  intro Y Z
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply ((path p Y - path p Z).norm_le (norm_nonneg (Y - Z))).mpr
  intro t
  exact difference_bound_profiles p Y Z t t (norm_nonneg _) (fun a ↦ (Y - Z).norm_coe_le_norm _)

/-- A measurable continuous parameter field gives a strongly measurable
physical path in both L2 and L-infinity, despite the latter space being
nonseparable. The map from the separable parameter-function space is
already a proved contraction. -/
theorem stronglyMeasurable_random_path {Ω : Type*} [MeasurableSpace Ω]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (Y : Parameter → Ω → ℝ)
    (hm : ∀ q, Measurable (Y q)) (hc : ∀ ω, Continuous (fun q ↦ Y q ω)) :
    StronglyMeasurable (fun ω ↦ path p ⟨fun q ↦ Y q ω, hc ω⟩) := by
  let Q (ω : Ω) : C(Parameter, ℝ) := ⟨fun q ↦ Y q ω, hc ω⟩
  have hQ : StronglyMeasurable Q :=
    (ContinuousMap.measurable_iff_eval.mpr hm).stronglyMeasurable
  exact (lipschitz_path p).continuous.comp_stronglyMeasurable hQ

end SHEStochastic.PhysicalHeatParameterSection
