module

public import SHE.LocalizedItoTest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.LocalizedItoTest
open Set MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/-- Subtraction preserves the actual localized finite-Itô test class. -/
theorem SmoothTimeTest.sub {a b : ℝ} {G dG F dF : ℝ→E→ℝ}
    (hG : SmoothTimeTest a b G dG) (hF : SmoothTimeTest a b F dF) :
    SmoothTimeTest a b (fun t z=>G t z-F t z) (fun t z=>dG t z-dF t z) := by
  refine ⟨hG.continuous.sub hF.continuous,hG.uniformSmooth.sub hF.uniformSmooth,
    fun z=>(hG.time_absolutelyContinuous z).sub (hF.time_absolutelyContinuous z),?_,
    hG.derivative_measurable.sub hF.derivative_measurable,
    fun t=>(hG.derivative_state_continuous t).sub (hF.derivative_state_continuous t),?_⟩
  · filter_upwards [hG.time_derivative,hF.time_derivative] with t ht hf htm z
    exact (ht htm z).sub (hf htm z)
  · obtain ⟨v,hv,hvb⟩:=hG.derivative_envelope
    obtain ⟨w,hw,hwb⟩:=hF.derivative_envelope
    refine ⟨fun t=>v t+w t,hv.add hw,fun t ht=>⟨add_nonneg (hvb t ht).1 (hwb t ht).1,fun z=>?_⟩⟩
    exact (norm_sub_le _ _).trans ((add_le_add ((hvb t ht).2 z) ((hwb t ht).2 z)).trans_eq (by ring))

end SHE.LocalizedItoTest
