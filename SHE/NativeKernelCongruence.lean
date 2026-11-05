module

public import SHE.NativeRandomKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeKernelCongruence
open MeasureTheory StoppedFourier NativeRandomKernel
local instance nativeKernelCongruence_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- The total L² realization depends only on its actual section,
including when the section is outside L² and the total definition is zero. -/
theorem realize_congr {P Q X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ν : Measure X)
    (F : P×X→E) (G : Q×X→E) (p : P) (q : Q) (h : ∀ x,F (p,x)=G (q,x)) :
    HilbertL2Fields.realize (ν:=ν) F p=HilbertL2Fields.realize (ν:=ν) G q := by
  have he : (fun x=>F (p,x))=(fun x=>G (q,x)):=funext h
  classical
  by_cases hf : MemLp (fun x=>F (p,x)) 2 ν
  · have hg : MemLp (fun x=>G (q,x)) 2 ν:=he ▸ hf
    simp only [HilbertL2Fields.realize,dif_pos hf,dif_pos hg]
    apply Lp.ext
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    rw [hx,hy,h]
  · have hg : ¬MemLp (fun x=>G (q,x)) 2 ν:=fun hg=>hf (he ▸ hg)
    simp only [HilbertL2Fields.realize,dif_neg hf,dif_neg hg]

theorem realize_complex_congr {P Q X : Type*} [MeasurableSpace X] (ν : Measure X)
    (F : P×X→ℂ) (G : Q×X→ℂ) (p : P) (q : Q) (h : ∀ x,F (p,x)=G (q,x)) :
    MeasurableL2Field.realizeL2 (ν:=ν) F p=MeasurableL2Field.realizeL2 (ν:=ν) G q := by
  have he : (fun x=>F (p,x))=(fun x=>G (q,x)):=funext h
  classical
  by_cases hf : MemLp (fun x=>F (p,x)) 2 ν
  · have hg : MemLp (fun x=>G (q,x)) 2 ν:=he ▸ hf
    simp only [MeasurableL2Field.realizeL2,dif_pos hf,dif_pos hg]
    apply Lp.ext
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    rw [hx,hy,h]
  · have hg : ¬MemLp (fun x=>G (q,x)) 2 ν:=fun hg=>hf (he ▸ hg)
    simp only [MeasurableL2Field.realizeL2,dif_neg hf,dif_neg hg]

/-- Equality of native scalar kernel sections gives equality of the
literal synthesized integral operators even across parameter spaces. -/
theorem operator_congr {P Q : Type*} [MeasurableSpace P] [MeasurableSpace Q]
    (F : P×(HeatCircle×HeatCircle)→ℂ) (G : Q×(HeatCircle×HeatCircle)→ℂ)
    (p : P) (q : Q) (h : ∀ y x,F (p,(y,x))=G (q,(y,x))) :
    integralOperator F p=integralOperator G q := by
  have hc (y : HeatCircle) : column F (p,y)=column G (q,y) := by
    unfold column NativeRandomRows.nativeRow RandomRowEnergy.row
    congr 1
    apply realize_complex_congr
    intro x
    exact h y _
  unfold integralOperator kernel
  congr 1
  exact realize_congr _ _ _ _ _ hc

end SHE.NativeKernelCongruence
