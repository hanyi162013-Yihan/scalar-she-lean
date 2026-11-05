module

public import SHE.LocalizedItoTest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.LocalizedItoTest
open Set MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/-- Prefix restriction of an actual localized finite-Itô test. -/
theorem SmoothTimeTest.prefix {a b c : ℝ} {G dG : ℝ→E→ℝ}
    (hG : SmoothTimeTest a b G dG) (hac : a≤c) (hcb : c≤b) :
    SmoothTimeTest a c G dG := by
  have hab : a≤b:=hac.trans hcb
  have hs : uIcc a c⊆uIcc a b := by
    rw [uIcc_of_le hac,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hcb
  refine ⟨hG.continuous,hG.uniformSmooth,fun z=>(hG.time_absolutelyContinuous z).mono hs,?_,
    hG.derivative_measurable,hG.derivative_state_continuous,?_⟩
  · filter_upwards [hG.time_derivative] with t ht htm z
    exact ht ⟨htm.1,htm.2.trans_le hcb⟩ z
  · obtain ⟨m,hm,hmb⟩:=hG.derivative_envelope
    exact ⟨m,hm.mono_set hs,fun t ht=>hmb t ⟨ht.1,ht.2.trans_le hcb⟩⟩

end SHE.LocalizedItoTest
