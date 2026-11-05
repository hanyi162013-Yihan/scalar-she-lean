module

public import SHE.GaussianWeightKernel
public import SHE.StoppedCanonicalScore

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeHeatSpan
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier HeatTorusKernel
open scoped BigOperators
local instance nativeHeatKernel_nativePositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance nativeHeatKernel_unitPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The genuine normalized positive heat kernel on the native period-2π
circle, obtained by the exact physical clock and Haar isometry. -/
def kernel (t : ℝ) (ht : 0 < t) (a : HeatCircle) : C(HeatCircle, ℂ) :=
  (HeatMarkov.kernel (clock t) (clock_pos ht)).comp
    ⟨fun x => unitCenter x - unitCenter a, (CircleNormalization.continuous_scale (2*Real.pi) 1).sub continuous_const⟩

theorem kernel_norm_mass {t : ℝ} (ht : 0 < t) (a : HeatCircle) :
    (∫ x, ‖kernel t ht a x‖ ∂haarAddCircle) = 1 := by
  have he := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).integral_comp
    (CircleNormalization.scaleMeasurableEquiv (2*Real.pi) 1).measurableEmbedding
    (fun x : UnitAddCircle => ‖HeatMarkov.kernel (clock t) (clock_pos ht) (x-unitCenter a)‖)
  exact he.trans ((integral_sub_right_eq_self (μ := haarAddCircle)
    (fun x : UnitAddCircle => ‖HeatMarkov.kernel (clock t) (clock_pos ht) x‖) (unitCenter a)).trans
      (HeatMarkov.kernel_norm_mass (clock_pos ht)))

theorem kernel_physical_ae {t : ℝ} (ht : 0 < t) (a : HeatCircle) :
    (kernel t ht a : HeatCircle → ℂ) =ᵐ[haarAddCircle] ProfileVariance.heatPhysical t a := by
  have hclock : 4*Real.pi^2*clock t = t := by unfold clock; field_simp
  have hphys := StoppedCanonicalScore.unitHeatKernel_physical_ae (clock_pos ht) (unitCenter a)
  rw [scale_inverse a, hclock] at hphys
  have hkernel := HeatMarkov.unitHeatKernel_ae (clock_pos ht) (unitCenter a)
  have he : ∀ᵐ x : UnitAddCircle ∂haarAddCircle,
      HeatMarkov.kernel (clock t) (clock_pos ht) (x-unitCenter a) =
        ProfileVariance.heatPhysical t a (CircleNormalization.scale 1 (2*Real.pi) x) := by
    filter_upwards [hphys,hkernel] with x hx hy
    exact hy.symm.trans hx
  have hp := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae he
  filter_upwards [hp] with x hx
  change HeatMarkov.kernel (clock t) (clock_pos ht) (unitCenter x-unitCenter a) = _
  change HeatMarkov.kernel (clock t) (clock_pos ht) (unitCenter x-unitCenter a) =
    ProfileVariance.heatPhysical t a (CircleNormalization.scale 1 (2*Real.pi) (unitCenter x)) at hx
  rwa [scale_inverse x] at hx

theorem weight_le_kernel {t : ℝ} (ht : 0 < t) (a x : HeatCircle) :
    weight t a x ≤ Real.sqrt (8*Real.pi) * ‖kernel (2*t) (by positivity) a x‖ := by
  have he : clock (2*t) = 2*clock t := by unfold clock; ring
  change GlobalTorusHeatSpan.weight (clock t) (unitCenter a) (unitCenter x) ≤
    Real.sqrt (8*Real.pi) * ‖HeatMarkov.kernel (clock (2*t)) _ (unitCenter x-unitCenter a)‖
  simpa only [he] using GaussianWeightKernel.weight_le_kernel (clock_pos ht) (unitCenter a) (unitCenter x)

theorem weight_le_physical_ae {t : ℝ} (ht : 0 < t) (a : HeatCircle) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      weight t a x ≤ Real.sqrt (8*Real.pi) * ‖ProfileVariance.heatPhysical (2*t) a x‖ := by
  filter_upwards [kernel_physical_ae (by positivity : 0 < 2*t) a] with x hx
  simpa only [hx] using weight_le_kernel ht a x

end SHE.NativeHeatSpan
