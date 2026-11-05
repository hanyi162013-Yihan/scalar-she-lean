module

public import SHE.PositiveGapObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HeatAgeContinuity
open Set Filter MeasureTheory StoppedFourier
open scoped Topology ENNReal
local instance heatAgeContinuity_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance heatAgeContinuity_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance heatAgeContinuity_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance heatAgeContinuity_unitSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance heatAgeContinuity_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

def heat (t : ℝ) (v : CircleL2) : CircleL2 :=
  CircleNormalization.push (CircleHeat.heat (t/NativeHeatObservation.timeScale) (CircleNormalization.push.symm v))

theorem continuous_heat_action : Continuous (fun p : ℝ × CircleL2 => heat p.1 p.2) := by
  have hp : Continuous (fun p : ℝ × CircleL2 =>
      (p.1/NativeHeatObservation.timeScale,CircleNormalization.push.symm p.2)) :=
    (continuous_fst.div_const _).prodMk (CircleNormalization.push.symm.continuous.comp continuous_snd)
  have hh := CircleHeat.continuous_heat_action.comp hp
  exact CircleNormalization.push.continuous.comp hh

theorem heat_eq {t : ℝ} (ht : 0 ≤ t) (v : CircleL2) : heat t v=circleHeatOperator t ht v := by
  unfold heat
  rw [CircleNormalization.push_heat _ (div_nonneg ht NativeHeatObservation.timeScale_pos.le),
    LinearIsometryEquiv.apply_symm_apply]
  have he : (2*Real.pi)^2*(t/NativeHeatObservation.timeScale)=t := by
    change NativeHeatObservation.timeScale*(t/NativeHeatObservation.timeScale)=t
    field_simp [NativeHeatObservation.timeScale_pos.ne']
  simp only [he]

theorem continuousAt_circleHeat_age {t : ℝ} (ht : 0 < t) (x : HeatCircle) :
    ContinuousAt (fun s : ℝ => circleHeat s x) t := by
  let a := t/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : Continuous (fun s : ℝ => (s-a,circleHeat a x)) :=
    (continuous_id.sub continuous_const).prodMk continuous_const
  have hc := continuous_heat_action.comp hp
  have he : (fun s : ℝ => circleHeat s x)=ᶠ[𝓝 t]
      (fun s : ℝ => heat (s-a) (circleHeat a x)) := by
    filter_upwards [eventually_gt_nhds (show a<t by dsimp [a]; linarith)] with s hs
    rw [heat_eq (sub_nonneg.mpr hs.le),circleHeatOperator_heat (sub_nonneg.mpr hs.le) ha,
      sub_add_cancel]
  exact hc.continuousAt.congr_of_eventuallyEq he

theorem continuousAt_heatPhysical_age {t : ℝ} (ht : 0 < t) (x y : HeatCircle) :
    ContinuousAt (fun s : ℝ => ProfileVariance.heatPhysical s x y) t := by
  have hhalf : 0 < t/2 := by positivity
  have hd : ContinuousAt (fun s : ℝ => s/2) t := (continuous_id.div_const 2).continuousAt
  have h₀ := (continuousAt_circleHeat_age (t := t/2) hhalf y).comp
    (f := fun s : ℝ => s/2) (x := t) hd
  have h₁ := (continuousAt_circleHeat_age (t := t/2) hhalf x).comp
    (f := fun s : ℝ => s/2) (x := t) hd
  have hc := h₀.inner (𝕜 := ℂ) h₁
  have he : (fun s : ℝ => ProfileVariance.heatPhysical s x y)=ᶠ[𝓝 t]
      (fun s : ℝ => inner ℂ (circleHeat (s/2) y) (circleHeat (s/2) x)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [circleHeat_cross_gram (by positivity) (by positivity)]
    rw [show s/2+s/2=s by ring]
    rfl
  exact hc.congr_of_eventuallyEq he

end SHE.HeatAgeContinuity
