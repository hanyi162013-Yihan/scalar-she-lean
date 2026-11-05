module

public import SHE.NativeKernelAction
public import SHE.HaarSeparatedGenerations

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeKernelConversion_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeKernelConversion_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeKernelConversion_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
variable {Ω : Type*} [MeasurableSpace Ω]

def unitOperator (F : Ω × (HeatCircle × HeatCircle) → ℂ) (ω : Ω) :
    CircleHeat.CircleL2 →L[ℂ] CircleHeat.CircleL2 :=
  CircleNormalization.push.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((integralOperator F ω).comp CircleNormalization.push.toLinearIsometry.toContinuousLinearMap)

def unitKernel (F : Ω × (HeatCircle × HeatCircle) → ℂ) (ω : Ω)
    (p : UnitAddCircle × UnitAddCircle) : ℂ :=
  F (ω,(CircleNormalization.scale 1 (2*π) p.2,CircleNormalization.scale 1 (2*π) p.1))

theorem unitCenter_scale (x : UnitAddCircle) :
    NativeHeatSpan.unitCenter (CircleNormalization.scale 1 (2*π) x)=x := by
  apply (CircleNormalization.scale 1 (2*π)).injective
  exact NativeHeatSpan.scale_inverse _

theorem push_symm_ae (f : CircleL2) :
    (CircleNormalization.push.symm f : UnitAddCircle → ℂ)=ᵐ[haarAddCircle]
      fun x => f (CircleNormalization.scale 1 (2*π) x) := by
  rw [CircleNormalization.push,CircleNormalization.equivalence_symm_apply]
  exact CircleNormalization.pull_ae 1 (2*π) f

/-- Native physical kernel action transfers exactly to the unit-circle
kernel action, including the normalized Haar measure. -/
theorem unitOperator_ae {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) (v : CircleHeat.CircleL2) :
    (unitOperator F ω v : UnitAddCircle → ℂ)=ᵐ[haarAddCircle]
      fun x => ∫ y : UnitAddCircle, unitKernel F ω (x,y)*v y ∂haarAddCircle := by
  have hp := (CircleNormalization.scale_measurePreserving 1 (2*π)).quasiMeasurePreserving.ae
    (integralOperator_ae hF hB hb ω (CircleNormalization.push v))
  have hv : ∀ᵐ y : UnitAddCircle ∂haarAddCircle,
      CircleNormalization.push v (CircleNormalization.scale 1 (2*π) y)=v y := by
    have hh := (push_symm_ae (CircleNormalization.push v)).symm
    rw [LinearIsometryEquiv.symm_apply_apply] at hh
    exact hh
  filter_upwards [push_symm_ae (integralOperator F ω (CircleNormalization.push v)),hp] with x hx ha
  change CircleNormalization.push.symm (integralOperator F ω (CircleNormalization.push v)) x=_
  rw [hx,ha]
  rw [← (CircleNormalization.scale_measurePreserving 1 (2*π)).integral_comp
    (CircleNormalization.scaleMeasurableEquiv 1 (2*π)).measurableEmbedding
    (fun y : HeatCircle => F (ω,(y,CircleNormalization.scale 1 (2*π) x))*CircleNormalization.push v y)]
  apply integral_congr_ae
  filter_upwards [hv] with y hy
  change F (ω,(CircleNormalization.scale 1 (2*π) y,CircleNormalization.scale 1 (2*π) x))*
    CircleNormalization.push v (CircleNormalization.scale 1 (2*π) y)=unitKernel F ω (x,y)*v y
  rw [hy]
  rfl

/-- A pathwise native heat envelope constructs the actual unit-circle
heat-dominated kernel package used by the signed two-time Haar theorem.
No Schur or Sobolev estimate is assumed in this package. -/
def dominatedKernel {τ K B : ℝ} (hτ : 0 < τ)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F) (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω)
    (hsharp : ∀ y x, ‖F (ω,(y,x))‖ ≤ K*‖ProfileVariance.heatPhysical τ y x‖) :
    HeatDominatedKernel (NativeHeatSpan.clock τ) K (NativeHeatSpan.clock_pos hτ) where
  operator := unitOperator F ω
  kernel := unitKernel F ω
  measurable_kernel := hF.comp (measurable_const.prodMk
    (((CircleNormalization.continuous_scale 1 (2*π)).measurable.comp measurable_snd).prodMk
      ((CircleNormalization.continuous_scale 1 (2*π)).measurable.comp measurable_fst)))
  kernel_bound := by
    intro x y
    have h := hsharp (CircleNormalization.scale 1 (2*π) y) (CircleNormalization.scale 1 (2*π) x)
    rw [← NativeHeatSpan.kernel_eq_physical hτ] at h
    calc
      _ = ‖F (ω,(CircleNormalization.scale 1 (2*π) y,CircleNormalization.scale 1 (2*π) x))‖ := rfl
      _ ≤ _ := h
      _ = _ := by
        change K*‖HeatMarkov.kernel (NativeHeatSpan.clock τ) _
          (NativeHeatSpan.unitCenter (CircleNormalization.scale 1 (2*π) x)-
            NativeHeatSpan.unitCenter (CircleNormalization.scale 1 (2*π) y))‖=
          K*‖HeatMarkov.kernel (NativeHeatSpan.clock τ) _ (y-x)‖
        rw [unitCenter_scale,unitCenter_scale]
        have he := HeatMarkov.kernel_neg (NativeHeatSpan.clock_pos hτ) (y-x)
        simpa only [neg_sub] using congrArg (fun z : ℂ => K*‖z‖) he
  representation := unitOperator_ae hF hB hb ω

end SHE.NativeRandomKernel
