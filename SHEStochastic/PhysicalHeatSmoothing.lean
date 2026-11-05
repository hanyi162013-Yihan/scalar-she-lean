module

public import SHE.HeatAgeContinuity
public import SHE.PhysicalMeanSemigroup
public import SHEStochastic.PhysicalHeatParameterSection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.PhysicalHeatSmoothing
open MeasureTheory SHE SHE.StoppedFourier SHE.PhysicalProfile AddCircle Filter Set
open scoped ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem point_bound {r : ℝ} (hr : 0 < r) (d : CircleL2) (x : HeatCircle) :
    |physicalHeatMean d (r, x)| ≤ ‖circleHeat r (0 : HeatCircle)‖ * ‖d‖ := by
  rw [physicalHeatMean_eq hr]
  have hc : ‖circleHeat r x‖ = ‖circleHeat r (0 : HeatCircle)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (circleHeat_norm_sq_center r x 0)
  exact (Complex.abs_re_le_norm _).trans (by simpa only [hc] using
    (norm_inner_le_norm (𝕜 := ℂ) (circleHeat r x) d))

theorem memLp (p : ℝ≥0∞) {r : ℝ} (hr : 0 < r) (d : CircleL2) :
    MemLp (fun x : HeatCircle ↦ physicalHeatMean d (r, x)) p haarAddCircle :=
  MemLp.of_bound ((physicalHeatMean_measurable d).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (‖circleHeat r (0 : HeatCircle)‖ * ‖d‖) (Eventually.of_forall (point_bound hr d))

/-- The actual positive-time heat mean in L2 or L-infinity, with no
regularity assumption on the initial L2 class. -/
def value (p : ℝ≥0∞) (r : ℝ) (hr : 0 < r) (d : CircleL2) :
    Lp ℝ p (haarAddCircle (T := 2 * Real.pi)) := (memLp p hr d).toLp _

theorem value_ae (p : ℝ≥0∞) (r : ℝ) (hr : 0 < r) (d : CircleL2) :
    value p r hr d =ᵐ[haarAddCircle] fun x ↦ physicalHeatMean d (r, x) :=
  (memLp p hr d).coeFn_toLp

theorem difference_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (r : ℝ) (hr : 0 < r)
    (d e : CircleL2) :
    ‖value p r hr d - value p r hr e‖ ≤ ‖circleHeat r (0 : HeatCircle)‖ * ‖d - e‖ := by
  have hh : ∀ᵐ x ∂haarAddCircle, ‖(value p r hr d - value p r hr e) x‖ ≤
      ‖circleHeat r (0 : HeatCircle)‖ * ‖d - e‖ := by
    filter_upwards [value_ae p r hr d, value_ae p r hr e,
      Lp.coeFn_sub (value p r hr d) (value p r hr e)] with x hd he hsub
    rw [hsub, Pi.sub_apply, hd, he, Real.norm_eq_abs, physicalHeatMean_difference hr]
    exact point_bound hr (d - e) x
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.one_rpow,
    NNReal.coe_one, Real.one_rpow, one_mul] using
    Lp.norm_le_of_ae_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hh

theorem lipschitz_value (p : ℝ≥0∞) [Fact (1 ≤ p)] (r : ℝ) (hr : 0 < r) :
    LipschitzWith ‖circleHeat r (0 : HeatCircle)‖₊ (value p r hr) := by
  apply LipschitzWith.of_dist_le_mul
  intro d e
  simpa only [dist_eq_norm, coe_nnnorm] using difference_bound p r hr d e

/-- Fixed positive smoothing followed by the strongly continuous L2
semigroup recovers the original heat mean exactly. -/
theorem value_heat (p : ℝ≥0∞) {r q : ℝ} (hr : 0 < r) (hq : 0 ≤ q) (d : CircleL2) :
    value p r hr (HeatAgeContinuity.heat q d) = value p (q + r) (by linarith) d := by
  apply Lp.ext
  filter_upwards [value_ae p r hr (HeatAgeContinuity.heat q d),
    value_ae p (q + r) (by linarith) d] with x hx hy
  rw [hx, hy, HeatAgeContinuity.heat_eq hq, PhysicalMeanSemigroup.heatMean_heat hr hq]

/-- Positive-time L-infinity continuity is a consequence of fixed-age
L2-to-uniform smoothing and L2 strong continuity. It asserts nothing
about L-infinity convergence to rough initial data at time zero. -/
theorem continuous_value (p : ℝ≥0∞) [Fact (1 ≤ p)] (d : CircleL2) :
    Continuous (fun t : Ioi (0 : ℝ) ↦ value p t.val t.property d) := by
  rw [continuous_iff_continuousAt]
  intro t
  let r : ℝ := t.val / 2
  have ht : 0 < t.val := t.property
  have hr : 0 < r := div_pos ht (by norm_num)
  have hrt : r < t.val := by dsimp [r]; linarith
  have hv : Continuous (fun s : Ioi (0 : ℝ) ↦ (s.val : ℝ)) := continuous_subtype_val
  have hrc : Continuous (fun _ : Ioi (0 : ℝ) ↦ r) := continuous_const
  have hs : Continuous (fun s : Ioi (0 : ℝ) ↦ (s.val - r : ℝ)) := hv.sub hrc
  have hd : Continuous (fun _ : Ioi (0 : ℝ) ↦ d) := continuous_const
  have hshift : Continuous (fun s : Ioi (0 : ℝ) ↦ (s.val - r, d)) := hs.prodMk hd
  have hh := HeatAgeContinuity.continuous_heat_action.comp hshift
  have hc := (lipschitz_value p r hr).continuous.comp hh
  apply hc.continuousAt.congr_of_eventuallyEq
  have hn : ∀ᶠ s : Ioi (0 : ℝ) in 𝓝 t, r < s.val :=
    (continuous_subtype_val.tendsto t) (eventually_gt_nhds hrt)
  filter_upwards [hn] with s hs
  have he := value_heat p hr (sub_nonneg.mpr hs.le) d
  change value p s.val s.property d = value p r hr (HeatAgeContinuity.heat (s.val - r) d)
  simpa only [sub_add_cancel] using he.symm

end SHEStochastic.PhysicalHeatSmoothing
