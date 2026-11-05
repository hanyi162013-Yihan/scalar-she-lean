module

public import SHE.HeatFieldApproximation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.HeatFieldTestLimit
open Set MeasureTheory AddCircle StoppedFourier NativeHeatObservation Filter Topology
open DyadicApproximation HeatFieldApproximation
local instance heatFieldTestLimit_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance heatFieldTestLimit_realSigma : MeasurableSpace RealL2 := borel _
local instance heatFieldTestLimit_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance heatFieldTestLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance heatFieldTestLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]
variable (U : P→RealL2) (hU : Measurable U)
variable (F : HeatCircle×ℝ→ℝ) (hF : Measurable F)

def difference (ε : ℝ) (q : P×HeatCircle) : ℝ :=
  F (q.2,PhysicalProfile.physicalHeatMean (embed (U q.1)) (ε,q.2))-
    F (q.2,PredictableScalarField.nativeField U q)

include hU hF in
theorem difference_measurable (ε : ℝ) : Measurable (difference U F ε) := by
  have hp : Measurable (fun q : P×HeatCircle => (embed (U q.1),(ε,q.2))) :=
    ((embed.continuous.measurable.comp hU).comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)
  have hm := PhysicalProfile.physicalHeatMean_joint_measurable.comp hp
  exact (hF.comp (measurable_snd.prodMk hm)).sub
    (hF.comp (measurable_snd.prodMk (PredictableScalarField.nativeField_measurable hU)))

def error (ε : ℝ) (p : P) : ℝ := ∫ x,|difference U F ε (p,x)| ∂haarAddCircle

include hU hF in
theorem error_measurable (ε : ℝ) : Measurable (error U F ε) :=
  ((difference_measurable U hU F hF ε).norm.stronglyMeasurable.integral_prod_right').measurable

theorem error_nonneg (ε : ℝ) (p : P) : 0≤error U F ε p := integral_nonneg (fun _ => abs_nonneg _)

theorem error_bound_const {M : ℝ} (hM : ∀ x z,|F (x,z)|≤M) (ε : ℝ) (p : P) :
    error U F ε p≤2*M := by
  have hh := norm_integral_le_of_norm_le_const (μ := haarAddCircle)
    (f := fun x => |difference U F ε (p,x)|) (C := 2*M)
    (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (abs_sub _ _).trans ((add_le_add (hM _ _) (hM _ _)).trans_eq (by ring))))
  change ‖error U F ε p‖≤(2*M)*haarAddCircle.real univ at hh
  simpa [Real.norm_eq_abs,abs_of_nonneg (error_nonneg U F ε p)] using hh

include hU hF in
/-- A spatially varying bounded Lipschitz test still sees genuine L²
heat approximation. No pointwise regularity of the state is assumed. -/
theorem error_bound {M D : ℝ} (hM : ∀ x z,|F (x,z)|≤M) (hD : 0≤D)
    (hLip : ∀ x z w,|F (x,z)-F (x,w)|≤D*|z-w|) {ε : ℝ} (hε : 0<ε) (p : P) :
    error U F ε p≤D*‖NativeHeatObservation.heat ε (U p)-U p‖ := by
  have hm := (difference_measurable U hU F hF ε).comp ((measurable_const (a := p)).prodMk measurable_id)
  have hi : Integrable (fun x => |difference U F ε (p,x)|) haarAddCircle := by
    apply (integrable_const (2*M)).mono' hm.norm.aestronglyMeasurable
    filter_upwards with x
    change abs (abs (difference U F ε (p,x)))≤2*M
    rw [abs_abs]
    exact (abs_sub _ _).trans ((add_le_add (hM _ _) (hM _ _)).trans_eq (by ring))
  let d : CircleL2 := embed (NativeHeatObservation.heat ε (U p))-embed (U p)
  have hd := ((Lp.memLp d).integrable (by norm_num : (1:ENNReal)≤2)).norm.const_mul D
  calc
    error U F ε p ≤ ∫ x,D*‖d x‖ ∂haarAddCircle := by
      apply integral_mono_ae hi hd
      filter_upwards [heatMean_ae hε (U p),PredictableScalarField.nativeField_ae_state U p,
        Lp.coeFn_sub (embed (NativeHeatObservation.heat ε (U p))) (embed (U p))] with x hh hx hsub
      apply (hLip x _ _).trans
      apply mul_le_mul_of_nonneg_left _ hD
      rw [hh,hx]
      change |(embed (NativeHeatObservation.heat ε (U p)) x).re-(embed (U p) x).re|≤‖d x‖
      change d x=embed (NativeHeatObservation.heat ε (U p)) x-embed (U p) x at hsub
      rw [hsub,← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    _ ≤ D*‖d‖ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_norm_le_norm d) hD
    _ = _ := by dsimp only [d]; rw [← map_sub,embed_norm]

include hU hF in
theorem error_tendsto_zero {M D : ℝ} (hM : ∀ x z,|F (x,z)|≤M) (hD : 0≤D)
    (hLip : ∀ x z w,|F (x,z)-F (x,w)|≤D*|z-w|) (p : P) :
    Tendsto (fun ε => error U F ε p) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (fun ε : ℝ => D*‖NativeHeatObservation.heat ε (U p)-U p‖) :=
    continuous_const.mul (((PositiveGapObservations.continuous_heat_action.comp
      (continuous_id.prodMk continuous_const)).sub continuous_const).norm)
  have he : D*‖NativeHeatObservation.heat 0 (U p)-U p‖=0 := by
    simp [NativeHeatObservation.heat,RealHeat.realHeat_zero]
  have ht := hc.tendsto 0
  rw [he] at ht
  apply squeeze_zero' (Eventually.of_forall (error_nonneg U F · p)) ?_ (ht.mono_left inf_le_left)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact error_bound U hU F hF hM hD hLip hε p

include hU hF in
/-- Full sample/spatial L¹ convergence with only a finite sample
measure, even when the state has no integrable L² norm. -/
theorem integrated_error_tendsto_zero (ν : Measure P) [IsFiniteMeasure ν]
    {M D : ℝ} (hM : ∀ x z,|F (x,z)|≤M) (hD : 0≤D)
    (hLip : ∀ x z w,|F (x,z)-F (x,w)|≤D*|z-w|) :
    Tendsto (fun ε => ∫ p,error U F ε p ∂ν) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hh := tendsto_integral_filter_of_dominated_convergence (μ := ν) (fun _ : P => 2*M)
    (Eventually.of_forall (fun ε => (error_measurable U hU F hF ε).aestronglyMeasurable))
    (Eventually.of_forall (fun ε => Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (error_nonneg U F ε p)]
      exact error_bound_const U F hM ε p))) (integrable_const _)
    (Eventually.of_forall (error_tendsto_zero U hU F hF hM hD hLip))
  simpa only [integral_zero] using hh

end SHE.HeatFieldTestLimit
