module

public import SHE.PredictableScalarField
public import SHE.PositiveGapObservations
public import SHE.HeatCutoffStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.HeatFieldApproximation
open Set MeasureTheory AddCircle StoppedFourier ProfileL2 NativeHeatObservation Filter Topology
open DyadicApproximation
open scoped ENNReal
local instance heatFieldApproximation_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance heatFieldApproximation_realSigma : MeasurableSpace RealL2 := borel RealL2
local instance heatFieldApproximation_realBorel : BorelSpace RealL2 := ⟨rfl⟩

theorem heatMean_ae {ε : ℝ} (hε : 0 < ε) (v : RealL2) :
    (fun x => PhysicalProfile.physicalHeatMean (embed v) (ε,x))=ᵐ[haarAddCircle]
      (fun x => (embed (NativeHeatObservation.heat ε v) x).re) := by
  filter_upwards [heat_kernel_inner_ae hε (embed v)] with x hx
  rw [PhysicalProfile.physicalHeatMean_eq hε,embed_heat hε.le,hx]

theorem integral_norm_le_norm (d : CircleL2) : (∫ x,‖d x‖ ∂haarAddCircle) ≤ ‖d‖ := by
  have hh := integral_mul_normTwo_bound (Lp.memLp d).norm
    (memLp_const (1:ℝ) : MemLp (fun _ : HeatCircle => (1:ℝ)) 2 haarAddCircle)
  have hn : normTwo haarAddCircle (fun x => ‖d x‖)=‖d‖ := by
    rw [normTwo,← L2_norm_sq_eq_integral d,Real.sqrt_sq (norm_nonneg _)]
  have hc : normTwo haarAddCircle (fun _ : HeatCircle => (1:ℝ))=1 := by simp [normTwo]
  simp only [mul_one,hn,hc] at hh
  exact (le_abs_self _).trans hh

variable {P : Type*} (U : P → RealL2) (p : P)

def error (A : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∫ x : HeatCircle,|A (PhysicalProfile.physicalHeatMean (embed (U p)) (ε,x))-
    A (PredictableScalarField.nativeField U (p,x))| ∂haarAddCircle

theorem error_nonneg (A : ℝ → ℝ) (ε : ℝ) : 0 ≤ error U p A ε := integral_nonneg (fun _ => abs_nonneg _)

theorem error_bound {A : ℝ → ℝ} {M L : ℝ} (hM : ∀ z,|A z| ≤ M)
    (hL : 0 ≤ L) (hLip : ∀ z w,|A z-A w| ≤ L*|z-w|) {ε : ℝ} (hε : 0 < ε) :
    error U p A ε ≤ L*‖NativeHeatObservation.heat ε (U p)-U p‖ := by
  have hAc : Continuous A := by
    have hl : LipschitzWith ⟨L,hL⟩ A := LipschitzWith.of_dist_le_mul (by
      intro z w
      change |A z-A w| ≤ L*|z-w|
      exact hLip z w)
    exact hl.continuous
  have hmean : Measurable (fun x : HeatCircle => PhysicalProfile.physicalHeatMean (embed (U p)) (ε,x)) :=
    (PhysicalProfile.physicalHeatMean_measurable _).comp (measurable_const.prodMk measurable_id)
  have hx := PredictableScalarField.nativeField_ae_state U p
  have hfield : AEStronglyMeasurable (fun x => PredictableScalarField.nativeField U (p,x)) haarAddCircle :=
    (Complex.continuous_re.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (embed (U p)))).congr hx.symm
  have hI : Integrable (fun x : HeatCircle => |A (PhysicalProfile.physicalHeatMean (embed (U p)) (ε,x))-
      A (PredictableScalarField.nativeField U (p,x))|) haarAddCircle := by
    apply (integrable_const (2*M)).mono'
      (((hAc.measurable.comp hmean).aestronglyMeasurable.sub
        (hAc.comp_aestronglyMeasurable hfield)).norm)
    filter_upwards with x
    change abs (abs (A _-A _)) ≤ 2*M
    rw [abs_abs]
    exact (abs_sub _ _).trans ((add_le_add (hM _) (hM _)).trans_eq (by ring))
  let d : CircleL2 := embed (NativeHeatObservation.heat ε (U p))-embed (U p)
  have hdi := ((Lp.memLp d).integrable (by norm_num : (1:ENNReal) ≤ 2)).norm.const_mul L
  calc
    error U p A ε ≤ ∫ x : HeatCircle,L*‖d x‖ ∂haarAddCircle := by
      apply integral_mono_ae hI hdi
      filter_upwards [heatMean_ae hε (U p),hx,Lp.coeFn_sub (embed (NativeHeatObservation.heat ε (U p))) (embed (U p))]
        with x hh hx hd
      apply (hLip _ _).trans
      apply mul_le_mul_of_nonneg_left _ hL
      rw [hh,hx]
      change |(embed (NativeHeatObservation.heat ε (U p)) x).re-(embed (U p) x).re| ≤ ‖d x‖
      change d x=embed (NativeHeatObservation.heat ε (U p)) x-embed (U p) x at hd
      rw [hd,← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    _ ≤ L*‖d‖ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_norm_le_norm d) hL
    _ = _ := by dsimp only [d]; rw [← map_sub,embed_norm]

theorem error_tendsto_zero {A : ℝ → ℝ} {M L : ℝ} (hM : ∀ z,|A z| ≤ M)
    (hL : 0 ≤ L) (hLip : ∀ z w,|A z-A w| ≤ L*|z-w|) :
    Tendsto (error U p A) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (fun ε : ℝ => L*‖NativeHeatObservation.heat ε (U p)-U p‖) :=
    continuous_const.mul (((PositiveGapObservations.continuous_heat_action.comp
      (continuous_id.prodMk continuous_const)).sub continuous_const).norm)
  have he : L*‖NativeHeatObservation.heat 0 (U p)-U p‖=0 := by
    simp [NativeHeatObservation.heat,RealHeat.realHeat_zero]
  have ht := hc.tendsto 0
  rw [he] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (error_nonneg U p A)) ?_ (ht.mono_left inf_le_left)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact error_bound U p hM hL hLip hε

end SHE.HeatFieldApproximation
