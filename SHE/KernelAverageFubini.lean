module

public import SHE.NativeKernelAction

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.KernelAverageFubini
open Set MeasureTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance kernelAverageFubini_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
variable {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsFiniteMeasure ν]

/-- Genuine signed Fubini for old-space averaging of a bounded physical
kernel against an arbitrary L² input. -/
theorem integral_average_mul {F : A × HeatCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ a y, ‖F (a,y)‖ ≤ B) (v : CircleL2) :
    (∫ y : HeatCircle,(∫ a,F (a,y) ∂ν)*v y ∂haarAddCircle)=
      ∫ a,(∫ y : HeatCircle,F (a,y)*v y ∂haarAddCircle) ∂ν := by
  have hv : Integrable (v : HeatCircle → ℂ) haarAddCircle :=
    (Lp.memLp v).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hi : Integrable (fun p : A × HeatCircle => F p*v p.2) (ν.prod haarAddCircle) := by
    apply ((hv.norm.const_mul B).comp_snd ν).mono'
      (hF.aestronglyMeasurable.mul hv.aestronglyMeasurable.comp_snd)
    exact ae_of_all _ (fun p => by
      change ‖F p*v p.2‖ ≤ B*‖v p.2‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb p.1 p.2) (norm_nonneg _))
  calc
    _ = ∫ y : HeatCircle,(∫ a,F (a,y)*v y ∂ν) ∂haarAddCircle := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => (integral_mul_const (v y) (fun a => F (a,y))).symm)
    _ = _ := (integral_integral_swap hi).symm

end SHE.KernelAverageFubini
