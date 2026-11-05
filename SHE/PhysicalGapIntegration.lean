module

public import SHE.PhysicalOrderedGaps

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1900000
noncomputable section
open Classical

namespace SHE.PhysicalOrderedGaps
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalParentGeometry HistoryProductMeasure ActualMeanKernel OrderedGapCoordinates
open scoped BigOperators
local instance physicalGapIntegration_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem ordered_bounds (q T : ℝ) (k : ℕ) (t : Fin k → ℝ) (ht : ordered q T k t) :
    (∀ i,q < t i ∧ t i < T) ∧ q < boundary T k t ∧ boundary T k t ≤ T := by
  induction k with
  | zero => exact ⟨fun i => Fin.elim0 i,ht,le_rfl⟩
  | succ k ih =>
    have hold := ih (fun i => t i.succ) ht.2.2
    have hhead : t 0 < T := ht.2.1.trans_le hold.2.2
    refine ⟨?_,ht.1,hhead.le⟩
    intro i
    exact Fin.cases ⟨ht.1,hhead⟩ (fun j => hold.1 j) i

theorem ordered_mem_timeBox {base horizon q T : ℝ} (hq : base ≤ q) (hT : T ≤ horizon)
    (k : ℕ) (t : Fin k → ℝ) (ht : ordered q T k t) :
    t ∈ Set.univ.pi (fun _ : Fin k => Ioc base horizon) := by
  intro i _
  have hh := (ordered_bounds q T k t ht).1 i
  exact ⟨hq.trans_lt hh.1,hh.2.le.trans hT⟩

/-- The original finite product of restricted old-time volumes agrees
with full volume on the exact ordered support. No measure-normalizing
factor is introduced. -/
theorem ordered_box_integral {base horizon q T : ℝ} (hq : base ≤ q) (hT : T ≤ horizon)
    (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    (∫ t,if ordered q T k t then F t else 0
      ∂Measure.pi (fun _ : Fin k => volume.restrict (Ioc base horizon)))=
        ∫ t,if ordered q T k t then F t else 0 := by
  let box := Set.univ.pi (fun _ : Fin k => Ioc base horizon)
  have hbox : MeasurableSet box := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hm : Measure.pi (fun _ : Fin k => volume.restrict (Ioc base horizon))=
      (volume : Measure (Fin k → ℝ)).restrict box :=
    (Measure.restrict_pi_pi (μ:=fun _ : Fin k => (volume : Measure ℝ)) (fun _ => Ioc base horizon)).symm
  rw [hm,←integral_indicator hbox]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    by_cases ht : ordered q T k t
    · have hb := ordered_mem_timeBox hq hT k t ht
      simp only [indicator_apply,if_pos ht,box,if_pos hb]
    · simp only [indicator_apply,if_neg ht,ite_self])

theorem ordered_box_integrable_iff {base horizon q T : ℝ} (hq : base ≤ q) (hT : T ≤ horizon)
    (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    Integrable (fun t => if ordered q T k t then F t else 0)
      (Measure.pi (fun _ : Fin k => volume.restrict (Ioc base horizon))) ↔
        Integrable (fun t => if ordered q T k t then F t else 0) := by
  let box := Set.univ.pi (fun _ : Fin k => Ioc base horizon)
  let f := fun t => if ordered q T k t then F t else 0
  have hbox : MeasurableSet box := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hm : Measure.pi (fun _ : Fin k => volume.restrict (Ioc base horizon))=
      (volume : Measure (Fin k → ℝ)).restrict box :=
    (Measure.restrict_pi_pi (μ:=fun _ : Fin k => (volume : Measure ℝ)) (fun _ => Ioc base horizon)).symm
  have hind : box.indicator f=f := by
    funext t
    by_cases ht : ordered q T k t
    · have hb := ordered_mem_timeBox hq hT k t ht
      simp only [indicator_apply,f,if_pos ht,box,if_pos hb]
    · simp only [indicator_apply,f,if_neg ht,ite_self]
  rw [hm]
  exact (integrable_indicator_iff hbox).symm.trans (by rw [hind])

variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- Literal active recursive history integration is exactly the genuine
positive-gap simplex integral used by the all-order scalar calculus. -/
theorem active_gap_integral (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (q : ℝ) (hq : R.base ≤ q) (hTH : T ≤ R.horizon)
    (k : ℕ) (p : P) (x : Fin k → HeatCircle) (F : (Fin k → ℝ) → ℝ) :
    (∫ t,if StrictHistory L k (separated k (p,t,x)) ∧
        q < (carrier L k).terminal (separated k (p,t,x)) then F (gaps T k t) else 0
      ∂Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon)))=
        ∫ d,if (∀ i,0 < d i) ∧ (∑ i,d i) < T-q then F d else 0 := by
  simp_rw [strict_active_iff_ordered L T hT q hq]
  rw [ordered_box_integral hq hTH,OrderedGapCoordinates.ordered_integral]

theorem active_gap_integrable_iff (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (q : ℝ) (hq : R.base ≤ q) (hTH : T ≤ R.horizon)
    (k : ℕ) (p : P) (x : Fin k → HeatCircle) (F : (Fin k → ℝ) → ℝ) :
    Integrable (fun t => if StrictHistory L k (separated k (p,t,x)) ∧
        q < (carrier L k).terminal (separated k (p,t,x)) then F (gaps T k t) else 0)
      (Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon))) ↔
        Integrable (fun d => if (∀ i,0 < d i) ∧ (∑ i,d i) < T-q then F d else 0) := by
  simp_rw [strict_active_iff_ordered L T hT q hq]
  exact (ordered_box_integrable_iff hq hTH k (fun t => F (gaps T k t))).trans
    (OrderedGapCoordinates.ordered_integrable_iff q T k F)

end SHE.PhysicalOrderedGaps
