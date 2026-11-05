module

public import SHE.NativeOutputTranslation
public import SHE.NativeHeatQuadratic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeHeatTranslation
open MeasureTheory SHE SHE.StoppedFourier SHE.NativeOutputTranslation AddCircle
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem commute {t : ℝ} (ht : 0 ≤ t) (z : HeatCircle) (f : CircleL2) :
    circleHeatOperator t ht (translate z f)=translate z (circleHeatOperator t ht f) := by
  apply (fourierBasis (T := 2*Real.pi)).repr.injective
  apply lp.ext
  funext l
  simp only [fourierBasis_repr,circleHeatOperator_fourierCoeff,fourierCoeff_translate]
  ring

theorem norm {t : ℝ} (ht : 0 ≤ t) (z : HeatCircle) (f : CircleL2) :
    ‖circleHeatOperator t ht (translate z f)‖=‖circleHeatOperator t ht f‖ := by
  rw [commute,LinearIsometry.norm_map]

/-- The heat energy has the same literal quadratic representation
after any common translation of its two physical arguments. -/
theorem quadratic {t : ℝ} (ht : 0 < t) (z : HeatCircle) (f : CircleL2) (F : HeatCircle → ℝ)
    (hf : (f : HeatCircle → ℂ)=ᵐ[haarAddCircle] fun x => (F x : ℂ)) :
    ‖circleHeatOperator (t/2) (by positivity) f‖^2=
      ∫ x : HeatCircle,∫ y : HeatCircle,NativeHeatQuadratic.K t ht (x,y)*F (x+z)*F (y+z)
        ∂haarAddCircle ∂haarAddCircle := by
  have hShift := (measurePreserving_add_right haarAddCircle z).quasiMeasurePreserving.ae hf
  have hF : (translate (-z) f : HeatCircle → ℂ)=ᵐ[haarAddCircle] fun x => (F (x+z) : ℂ) := by
    filter_upwards [translate_ae (-z) f,hShift] with x hx hfx
    simp only [sub_neg_eq_add] at hx
    exact hx.trans hfx
  have hh := NativeHeatQuadratic.energy ht (translate (-z) f) (fun x => F (x+z)) hF
  simpa only [norm (show 0 ≤ t/2 by positivity)] using hh

end SHEStochastic.NativeHeatTranslation
