module

public import SHE.HeatedDifferenceMoments
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatedCurrentInput
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation
open scoped ENNReal Topology
local instance heatEnergyFatou_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance heatEnergyFatou_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance heatEnergyFatou_realSigma : MeasurableSpace RealL2 := borel _
local instance heatEnergyFatou_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance heatEnergyFatou_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance heatEnergyFatou_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Genuine finite current energy follows from the checked positive-age
point moments by spatial Tonelli, heat strong continuity, and Fatou.
No zero-age pointwise representative is introduced. -/
theorem energy_of_heated_moments (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω→RealL2) (hV : Measurable V) {C : ℝ} (hC : 0≤C)
    (hp : ∀ τ,0<τ → ∀ x,
      Integrable (fun ω=>field τ V (ω,x)^2) μ ∧
        (∫ ω,field τ V (ω,x)^2 ∂μ)≤C) :
    Integrable (fun ω=>‖V ω‖^2) μ ∧ (∫ ω,‖V ω‖^2 ∂μ)≤C := by
  have hheated (τ : ℝ) (hτ : 0<τ) :
      (∫⁻ ω,ENNReal.ofReal (‖value τ V ω‖^2) ∂μ)≤ENNReal.ofReal C := by
    have hm := field_measurable τ hV
    have hi (ω : Ω) : Integrable (fun x=>field τ V (ω,x)^2) haarAddCircle := by
      have hmp : MemLp (fun x=>field τ V (ω,x)) 2 haarAddCircle :=
        MemLp.of_bound ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
          (‖circleHeat τ 0‖*‖V ω‖) (ae_of_all _ (fun x=>by
            change ‖field τ V (ω,x)‖≤_
            rw [Real.norm_eq_abs]
            exact field_bound τ V ω x))
      exact hmp.integrable_sq
    have he (ω : Ω) : ENNReal.ofReal (‖value τ V ω‖^2)=
        ∫⁻ x,ENNReal.ofReal (field τ V (ω,x)^2) ∂haarAddCircle := by
      rw [L2_norm_sq_eq_integral]
      have hev : (∫ x,‖value τ V ω x‖^2 ∂haarAddCircle)=∫ x,field τ V (ω,x)^2 ∂haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [value_ae hτ V ω] with x hx
        rw [hx,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      rw [hev]
      exact ofReal_integral_eq_lintegral_ofReal (hi ω) (ae_of_all _ (fun x=>sq_nonneg _))
    calc
      _=∫⁻ ω,∫⁻ x,ENNReal.ofReal (field τ V (ω,x)^2) ∂haarAddCircle ∂μ :=
        lintegral_congr_ae (ae_of_all _ he)
      _=∫⁻ x,∫⁻ ω,ENNReal.ofReal (field τ V (ω,x)^2) ∂μ ∂haarAddCircle :=
        lintegral_lintegral_swap ((hm.pow_const 2).ennreal_ofReal.aemeasurable)
      _≤∫⁻ _ : HeatCircle,ENNReal.ofReal C ∂haarAddCircle := by
        apply lintegral_mono
        intro x
        change (∫⁻ ω,ENNReal.ofReal (field τ V (ω,x)^2) ∂μ)≤ENNReal.ofReal C
        rw [←ofReal_integral_eq_lintegral_ofReal (hp τ hτ x).1
          (ae_of_all _ (fun ω=>sq_nonneg (field τ V (ω,x))))]
        exact ENNReal.ofReal_le_ofReal (hp τ hτ x).2
      _=ENNReal.ofReal C := by simp
  let rate : ℕ→ℝ := fun n=>1/((n:ℝ)+1)
  have hrate (n : ℕ) : 0<rate n := by dsimp only [rate];positivity
  have hrate0 : Tendsto rate atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f : ℕ→Ω→ENNReal := fun n ω=>ENNReal.ofReal (‖value (rate n) V ω‖^2)
  have hfm (n : ℕ) : Measurable (f n) := by
    have hv : Measurable (fun ω=>heat (rate n) (V ω)) := (heat (rate n)).continuous.measurable.comp hV
    exact ((embed.continuous.measurable.comp hv).norm.pow_const 2).ennreal_ofReal
  have hlim (ω : Ω) : Tendsto (fun n=>f n ω) atTop (𝓝 (ENNReal.ofReal (‖V ω‖^2))) := by
    have hc : Continuous (fun τ : ℝ=>‖RealHeat.realHeat (τ/timeScale) (V ω)‖^2) :=
      (RealHeat.continuous_realHeat_action.comp
        ((continuous_id.div_const timeScale).prodMk continuous_const)).norm.pow 2
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hc.continuousAt.tendsto.comp hrate0)
    simpa only [f,value,embed_norm,heat,zero_div,RealHeat.realHeat_zero,
      ContinuousLinearMap.id_apply,Function.comp_def] using hh
  have hfat : (∫⁻ ω,Filter.liminf (fun n=>f n ω) atTop ∂μ)≤
      Filter.liminf (fun n=>∫⁻ ω,f n ω ∂μ) atTop := lintegral_liminf_le hfm
  have hlimEq (ω : Ω) : Filter.liminf (fun n=>f n ω) atTop=ENNReal.ofReal (‖V ω‖^2) :=
    (hlim ω).liminf_eq
  simp_rw [hlimEq] at hfat
  have hb : Filter.liminf (fun n=>∫⁻ ω,f n ω ∂μ) atTop≤ENNReal.ofReal C :=
    Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently
      (Filter.Eventually.of_forall (fun n=>hheated (rate n) (hrate n))))
  exact RealMomentBound.integral_bound μ (fun ω=>‖V ω‖^2)
    (hV.norm.pow_const 2).aestronglyMeasurable (fun ω=>sq_nonneg _) hC (hfat.trans hb)

end SHE.HeatedCurrentInput
