module

public import SHE.ShiftedScoreArrays
public import SHE.PhysicalScoreProduct
public import SHE.HistoryProductMeasure
public import SHE.PairedTerminalTimeFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.PairedTimeTranslation
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain PhysicalChainArrays
  CoveredControlledLaw ShiftedWordGeometry

variable {X:Type} [MeasurableSpace X] {R Q:ReferenceData} {n:ℕ}
variable (L:Level R X n) (K:Level Q X n) (v:ℝ)
variable (hb:Q.base=R.base+v) (hT:∀x,K.terminal x=L.terminal x+v)

include hb hT in
theorem strict_shift (k:ℕ) (p:History X k):
    StrictHistory K k (shift v k p)↔StrictHistory L k p:=by
  induction k with
  | zero=>exact Iff.rfl
  | succ k ih=>
    change (StrictHistory K k (shift v k p.1) ∧
      Q.base<p.2.1+v ∧ p.2.1+v<(carrier K k).terminal (shift v k p.1))↔_
    rw [ih p.1,hb,terminal_shift L K v hb hT k p.1]
    simp only [add_lt_add_iff_right]
    rfl

include hb hT in
theorem timeWeight_shift (ell:ℝ) (C:ℕ→ℝ) (k:ℕ) (p:History X k):
    timeWeight K ell C k (shift v k p)=timeWeight L ell C k p:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    change timeWeight K ell C k (shift v k p.1)*
      (C k/(ell*((carrier K k).terminal (shift v k p.1)-
        (carrier K k).nodeTime (shift v (k+1) p))))=_
    rw [ih p.1,terminal_shift L K v hb hT k p.1,nodeTime_shift L K v hb hT k p]
    simp only [add_sub_add_right_eq_sub]
    rfl

theorem separated_shift (k:ℕ) (x:X) (t:Fin k→ℝ) (w:Fin k→HeatCircle):
    shift v k (HistoryProductMeasure.separated k (x,t,w))=
      HistoryProductMeasure.separated k (x,(fun j=>t j+v),w):=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    change (shift v k (HistoryProductMeasure.separated k (x,(fun j=>t j.succ),(fun j=>w j.succ))),
      (t 0+v,w 0))=_
    rw [ih]
    rfl

/-- Translation preserves the ORIGINAL restricted old-time product
measure. It carries no probability normalization or extra mass factor. -/
theorem pi_translation (a b:ℝ) (k:ℕ):
    MeasurePreserving (fun t:Fin k→ℝ=>fun j=>t j+v)
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc a b)))
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (a+v) (b+v)))):=by
  have ht:MeasurePreserving (fun t:ℝ=>t+v)
      (volume.restrict (Ioc a b)) (volume.restrict (Ioc (a+v) (b+v))):=by
    have hh:=(measurePreserving_add_right (volume:Measure ℝ) v).restrict_preimage
      (measurableSet_Ioc:MeasurableSet (Ioc (a+v) (b+v)))
    have he:(fun t:ℝ=>t+v) ⁻¹' Ioc (a+v) (b+v)=Ioc a b:=by
      ext t
      simp only [mem_preimage,mem_Ioc,add_lt_add_iff_right,add_le_add_iff_right]
    rw [he] at hh
    exact hh
  exact measurePreserving_pi _ _ (fun _:Fin k=>ht)

end SHE.PairedTimeTranslation
