module

public import SHE.PhysicalSpatialSections
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.HistoryProductMeasure
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories PhysicalScoreChain
  PhysicalParentGeometry
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P]

def assemble : (k : ℕ) → P × (Fin k → ℝ × HeatCircle) → History P k
  | 0,p => p.1
  | k+1,p => (assemble k (p.1,fun i => p.2 i.succ),p.2 0)

def nodes : (k : ℕ) → History P k → Fin k → ℝ × HeatCircle
  | 0,_ => Fin.elim0
  | k+1,p => Fin.cons p.2 (nodes k p.1)

theorem assemble_root_nodes (k : ℕ) (p : History P k) :
    assemble k (rootParameter k p,nodes k p)=p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (assemble k (rootParameter k p.1,fun i => nodes (k+1) p i.succ),nodes (k+1) p 0)=p
    simp only [nodes,Fin.cons_succ,Fin.cons_zero,ih p.1,Prod.eta]

theorem assemble_measurable (k : ℕ) : Measurable (assemble (P := P) k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    have ht : Measurable (fun p : P × (Fin (k+1) → ℝ × HeatCircle) =>
        (p.1,fun i : Fin k => p.2 i.succ)) :=
      measurable_fst.prodMk (Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd))
    exact (ih.comp ht).prodMk ((measurable_pi_apply 0).comp measurable_snd)

/-- The nested actual history measure is exactly the finite product of
its original node measures, in newest-coordinate-first order. -/
theorem assemble_measurePreserving (R : ReferenceData) (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    MeasurePreserving (assemble k)
      (μ.prod (Measure.pi (fun _ : Fin k => nodeMeasure R))) (historyMeasure R μ k) := by
  induction k with
  | zero =>
    have hpi : IsProbabilityMeasure (Measure.pi (fun _ : Fin 0 => nodeMeasure R)) := by
      rw [Measure.pi_of_empty _ (fun i => Fin.elim0 i)]
      infer_instance
    exact measurePreserving_fst (μ := μ) (ν := Measure.pi (fun _ : Fin 0 => nodeMeasure R))
  | succ k ih =>
    let ν := nodeMeasure R
    let π := Measure.pi (fun _ : Fin k => ν)
    have hsplit := (MeasurePreserving.id μ).prod
      (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => ν) 0)
    have hswap := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := π))
    have hassoc := (measurePreserving_prodAssoc μ π ν).symm
    have hfinish := ih.prod (MeasurePreserving.id ν)
    have hh := hfinish.comp (hassoc.comp (hswap.comp hsplit))
    convert! hh using 1

def separated (k : ℕ) (p : P × ((Fin k → ℝ) × (Fin k → HeatCircle))) : History P k :=
  assemble k (p.1,fun i => (p.2.1 i,p.2.2 i))

/-- Genuine time/space product disintegration for the original finite
history, with every time still distributed under its original restriction. -/
theorem separated_measurePreserving (R : ReferenceData) (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    MeasurePreserving (separated k)
      (μ.prod ((Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon))).prod
        (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)))) (historyMeasure R μ k) := by
  have hs := (measurePreserving_arrowProdEquivProdArrow ℝ HeatCircle (Fin k)
    (fun _ => volume.restrict (Ioc R.base R.horizon)) (fun _ => AddCircle.haarAddCircle)).symm
  have hh := (assemble_measurePreserving R μ k).comp ((MeasurePreserving.id μ).prod hs)
  convert! hh using 1

theorem separated_eq_replace (k : ℕ) (p : History P k) (x : Fin k → HeatCircle) :
    separated k (rootParameter k p,((fun i => (nodes k p i).1),x))=replaceSpace k p x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (assemble k (rootParameter k p.1,
      fun i => ((nodes (k+1) p i.succ).1,x i.succ)),((nodes (k+1) p 0).1,x 0)) =
      (replaceSpace k p.1 (fun i => x i.succ),p.2.1,x 0)
    simp only [nodes,Fin.cons_succ,Fin.cons_zero]
    exact congrArg (fun y => (y,p.2.1,x 0)) (ih p.1 (fun i => x i.succ))

end SHE.HistoryProductMeasure
