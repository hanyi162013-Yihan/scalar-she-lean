module

public import SHE.HeatEnergyFatou
public import SHE.WeightedSpatialMoments

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatedCurrentInput
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation
open scoped ENNReal Topology
local instance heatedHilbertMoments_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance heatedHilbertMoments_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance heatedHilbertMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance heatedHilbertMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance heatedHilbertMoments_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance heatedHilbertMoments_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Strong heat continuity and Fatou transfer any actual global heated
moment to the original Hilbert state, without a zero-age point value. -/
theorem norm_moment_of_heated_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω→RealL2) (hV : Measurable V) (m : ℕ) {C : ℝ} (hC : 0≤C)
    (hp : ∀ τ,0<τ → Integrable (fun ω=>‖value τ V ω‖^m) μ ∧
      (∫ ω,‖value τ V ω‖^m ∂μ)≤C) :
    Integrable (fun ω=>‖V ω‖^m) μ ∧ (∫ ω,‖V ω‖^m ∂μ)≤C := by
  let rate : ℕ→ℝ := fun n=>1/((n:ℝ)+1)
  have hrate (n : ℕ) : 0<rate n := by dsimp only [rate];positivity
  have hrate0 : Tendsto rate atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f : ℕ→Ω→ENNReal := fun n ω=>ENNReal.ofReal (‖value (rate n) V ω‖^m)
  have hfm (n : ℕ) : Measurable (f n) := by
    have hv : Measurable (fun ω=>heat (rate n) (V ω)) := (heat (rate n)).continuous.measurable.comp hV
    exact ((embed.continuous.measurable.comp hv).norm.pow_const m).ennreal_ofReal
  have hlim (ω : Ω) : Tendsto (fun n=>f n ω) atTop (𝓝 (ENNReal.ofReal (‖V ω‖^m))) := by
    have hc : Continuous (fun τ : ℝ=>‖RealHeat.realHeat (τ/timeScale) (V ω)‖^m) :=
      (RealHeat.continuous_realHeat_action.comp
        ((continuous_id.div_const timeScale).prodMk continuous_const)).norm.pow m
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hc.continuousAt.tendsto.comp hrate0)
    simpa only [f,value,embed_norm,heat,zero_div,RealHeat.realHeat_zero,
      ContinuousLinearMap.id_apply,Function.comp_def] using hh
  have hfat : (∫⁻ ω,Filter.liminf (fun n=>f n ω) atTop ∂μ)≤
      Filter.liminf (fun n=>∫⁻ ω,f n ω ∂μ) atTop := lintegral_liminf_le hfm
  have hlimEq (ω : Ω) : Filter.liminf (fun n=>f n ω) atTop=ENNReal.ofReal (‖V ω‖^m) :=
    (hlim ω).liminf_eq
  simp_rw [hlimEq] at hfat
  have hb : Filter.liminf (fun n=>∫⁻ ω,f n ω ∂μ) atTop≤ENNReal.ofReal C :=
    Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently
      (Filter.Eventually.of_forall (fun n=>by
        rw [←ofReal_integral_eq_lintegral_ofReal (hp (rate n) (hrate n)).1
          (ae_of_all _ (fun ω=>pow_nonneg (norm_nonneg _) m))]
        exact ENNReal.ofReal_le_ofReal (hp (rate n) (hrate n)).2)))
  exact RealMomentBound.integral_bound μ (fun ω=>‖V ω‖^m)
    (hV.norm.pow_const m).aestronglyMeasurable (fun ω=>pow_nonneg (norm_nonneg _) m) hC (hfat.trans hb)

/-- True all-order global Hilbert moments follow from positive-age
spatial point moments. Spatial Jensen precedes the heat/Fatou limit;
no pointwise value of the original L2 state is introduced. -/
theorem four_moment_of_heated_moments (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω→RealL2) (hV : Measurable V) (n : ℕ) (hn : 0<n) {C : ℝ} (hC : 0≤C)
    (hp : ∀ τ,0<τ → ∀ x,Integrable (fun ω=>field τ V (ω,x)^(4*n)) μ ∧
      (∫ ω,field τ V (ω,x)^(4*n) ∂μ)≤C) :
    Integrable (fun ω=>‖V ω‖^(4*n)) μ ∧ (∫ ω,‖V ω‖^(4*n) ∂μ)≤C := by
  apply norm_moment_of_heated_bound μ V hV (4*n) hC
  intro τ hτ
  have hm := field_measurable τ hV
  let G : Ω×HeatCircle→ℝ := fun z=>field τ V z^2
  have hG : Measurable G := hm.pow_const 2
  have he (ω : Ω) : ‖value τ V ω‖^2=∫ x,G (ω,x) ∂haarAddCircle := by
    rw [L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [value_ae hτ V ω] with x hx
    rw [hx,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hpow (ω : Ω) (x : HeatCircle) : |G (ω,x)|^(2*n)=field τ V (ω,x)^(4*n) := by
    rw [abs_of_nonneg (sq_nonneg _),←pow_mul]
    congr 1
    omega
  have hi : ∀ᵐ x : HeatCircle ∂haarAddCircle,Integrable (fun ω=>|G (ω,x)|^(2*n)) μ :=
    ae_of_all _ (fun x=>by simpa only [hpow] using (hp τ hτ x).1)
  have hb : ∀ᵐ x : HeatCircle ∂haarAddCircle,(∫ ω,|G (ω,x)|^(2*n) ∂μ)≤C*(1:ℝ)^(2*n) :=
    ae_of_all _ (fun x=>by simpa only [hpow,one_pow,mul_one] using (hp τ hτ x).2)
  have hh := WeightedSpatialMoments.nonnegative_envelope μ haarAddCircle G hG (fun _=>1)
    measurable_const (integrable_const _) (fun _=>by norm_num) n hn C hC hi hb
  have heq (ω : Ω) : |∫ x,G (ω,x) ∂haarAddCircle|^(2*n)=‖value τ V ω‖^(4*n) := by
    rw [←he,abs_of_nonneg (sq_nonneg _),←pow_mul]
    congr 1
    omega
  exact ⟨by simpa only [heq] using hh.1,by simpa only [heq,integral_const,probReal_univ,one_smul,one_pow,mul_one] using hh.2⟩

end SHE.HeatedCurrentInput
