module

public import SHE.ShiftedWordGeometry
public import SHE.ShiftedOldTimeMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.ShiftedHistoryMeasure
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories ShiftedWordGeometry
local instance shiftedHistoryMeasure_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X]

def equiv (v : ℝ) : (k : ℕ)→History X k≃ᵐHistory X k
  | 0=>MeasurableEquiv.refl _
  | k+1=>(equiv v k).prodCongr ((MeasurableEquiv.addRight v).prodCongr (MeasurableEquiv.refl _))

theorem equiv_apply (v : ℝ) (k : ℕ) (p : History X k) : equiv v k p=shift v k p := by
  induction k with
  | zero=>rfl
  | succ k ih=>exact congrArg (fun z=>(z,(p.2.1+v,p.2.2))) (ih p.1)

theorem node_preserving (R Q : ReferenceData) (v : ℝ)
    (hb : Q.base=R.base+v) (hh : Q.horizon=R.horizon+v) :
    MeasurePreserving ((MeasurableEquiv.addRight v).prodCongr (MeasurableEquiv.refl HeatCircle))
      (nodeMeasure R) (nodeMeasure Q) := by
  have ht := (measurePreserving_add_right (volume : Measure ℝ) v).restrict_preimage
    (measurableSet_Ioc : MeasurableSet (Ioc Q.base Q.horizon))
  have he : (fun t : ℝ=>t+v) ⁻¹' Ioc Q.base Q.horizon=Ioc R.base R.horizon := by
    rw [hb,hh]
    ext t
    simp only [mem_preimage,mem_Ioc,add_lt_add_iff_right,add_le_add_iff_right]
  rw [he] at ht
  exact ht.prod (MeasurePreserving.id AddCircle.haarAddCircle)

/-- The entire original nested history measure, not only a selected
ordered simplex or a probabilistic normalization, translates exactly. -/
theorem measurePreserving (R Q : ReferenceData) (v : ℝ)
    (hb : Q.base=R.base+v) (hh : Q.horizon=R.horizon+v) (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    MeasurePreserving (equiv v k) (historyMeasure R μ k) (historyMeasure Q μ k) := by
  induction k with
  | zero=>exact MeasurePreserving.id μ
  | succ k ih=>exact ih.prod (node_preserving R Q v hb hh)

theorem integral_translation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R Q : ReferenceData) (v : ℝ) (hb : Q.base=R.base+v) (hh : Q.horizon=R.horizon+v)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) (f : History X k→E) :
    (∫ p,f (shift v k p) ∂historyMeasure R μ k)=∫ p,f p ∂historyMeasure Q μ k := by
  have he:=(measurePreserving R Q v hb hh μ k).integral_comp' f
  simpa only [equiv_apply] using he

end SHE.ShiftedHistoryMeasure
