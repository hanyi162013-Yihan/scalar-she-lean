module

public import SHE.NativeRandomKernel
public import SHE.NativeRandomCap
public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance kernelActionFields_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance kernelActionFields_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance kernelActionFields_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance kernelActionFields_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance kernelActionFields_nativeSecondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance kernelActionFields_kernelSigma : MeasurableSpace KernelSpace := borel _
local instance kernelActionFields_kernelBorel : BorelSpace KernelSpace := ⟨rfl⟩
local instance kernelActionFields_kernelSecondCountable : SecondCountableTopology KernelSpace :=
  Lp.SecondCountableTopology
variable {P : Type*} [MeasurableSpace P]

attribute [local irreducible] KernelOperator.synthesis

/-- Parameter-dependent coarse bounds suffice for joint Borel kernel
actions. No uniform bound in old times, gaps, or random input is needed. -/
theorem kernel_measurable_bounded_sections {F : P×(HeatCircle×HeatCircle)→ℂ}
    (hF : Measurable F) (hb : ∀ p,∃ B : ℝ,∀ y x,‖F (p,(y,x))‖≤B) : Measurable (kernel F) := by
  classical
  choose B hB using hb
  have hcap0 (p : P) : 0≤B p := (norm_nonneg (F (p,(0,0)))).trans (hB p 0 0)
  have hcol : Measurable (column F) :=
    NativeRandomRows.nativeRow_measurable_cap (columnField_measurable hF) (fun p=>B p.1)
      (fun p x=>hB p.1 p.2 x)
  have hcolae (p : P) (y : HeatCircle) : (column F (p,y) : HeatCircle→ℂ)=ᵐ[haarAddCircle]
      fun x=>F (p,(y,x)) :=
    NativeRandomRows.nativeRow_ae_cap (columnField_measurable hF) (fun p=>B p.1)
      (fun p x=>hB p.1 p.2 x) (p,y)
  have hnorm (p : P) (y : HeatCircle) : ‖column F (p,y)‖≤B p := by
    have hh := Lp.norm_le_of_ae_bound (hcap0 p) ((hcolae p y).mono (fun x hx=>by
      rw [hx]
      exact hB p y x))
    simpa [measureUnivNNReal] using hh
  apply HilbertL2Fields.realize_measurable hcol
  intro p
  exact MemLp.of_bound ((hcol.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (B p) (ae_of_all _ (hnorm p))

theorem action_measurable {F : P×(HeatCircle×HeatCircle)→ℂ}
    (hF : Measurable F) (hb : ∀ p,∃ B : ℝ,∀ y x,‖F (p,(y,x))‖≤B)
    (v : P→CircleL2) (hv : Measurable v) :
    Measurable (fun p=>integralOperator F p (v p)) := by
  have hc : Continuous (fun z : KernelSpace×CircleL2=>KernelOperator.synthesis z.1 z.2) :=
    (KernelOperator.synthesis_continuous.comp continuous_fst).clm_apply continuous_snd
  change Measurable (fun p=>KernelOperator.synthesis (kernel F p) (v p))
  exact hc.measurable.comp ((kernel_measurable_bounded_sections hF hb).prodMk hv)

end SHE.NativeRandomKernel
