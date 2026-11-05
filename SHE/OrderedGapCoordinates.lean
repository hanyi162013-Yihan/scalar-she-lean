module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace SHE.OrderedGapCoordinates
open Set MeasureTheory
open scoped BigOperators ENNReal

/-- The oldest available upper endpoint for the newest coordinate.
Coordinates run newest first, as in the literal history product. -/
def boundary (T : ℝ) : (k : ℕ) → (Fin k → ℝ) → ℝ
  | 0, _ => T
  | _+1, t => t 0

def gaps (T : ℝ) : (k : ℕ) → (Fin k → ℝ) → Fin k → ℝ
  | 0, _ => Fin.elim0
  | k+1, t => Fin.cons (boundary T k (fun i => t i.succ)-t 0)
      (gaps T k (fun i => t i.succ))

theorem boundary_measurable (T : ℝ) (k : ℕ) : Measurable (boundary T k) := by
  cases k with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply 0

theorem gaps_measurable (T : ℝ) (k : ℕ) : Measurable (gaps T k) := by
  induction k with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ k ih =>
    have ht : Measurable (fun t : Fin (k+1) → ℝ => fun i : Fin k => t i.succ) := by fun_prop
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ((boundary_measurable T k).comp ht).sub (measurable_pi_apply 0)
    · exact (measurable_pi_apply j).comp (ih.comp ht)

def times (T : ℝ) : (k : ℕ) → (Fin k → ℝ) → Fin k → ℝ
  | 0, _ => Fin.elim0
  | k+1, d => let t := times T k (fun i=>d i.succ)
    Fin.cons (boundary T k t-d 0) t

theorem times_measurable (T : ℝ) (k : ℕ) : Measurable (times T k) := by
  induction k with
  | zero => exact Measurable.of_eval (fun i=>Fin.elim0 i)
  | succ k ih =>
    have ht : Measurable (fun d : Fin (k+1) → ℝ => times T k (fun i=>d i.succ)) :=
      ih.comp (by fun_prop)
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact ((boundary_measurable T k).comp ht).sub (measurable_pi_apply 0)
    · exact (measurable_pi_apply j).comp ht

theorem gaps_times (T : ℝ) (k : ℕ) (d : Fin k → ℝ) : gaps T k (times T k d)=d := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [times,gaps,Fin.cons_zero,Fin.cons_succ]
      ring
    · simpa only [times,gaps,Fin.cons_succ] using congrFun (ih (fun j=>d j.succ)) j

theorem times_gaps (T : ℝ) (k : ℕ) (t : Fin k → ℝ) : times T k (gaps T k t)=t := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    have ht : times T k (fun j=>gaps T (k+1) t j.succ)=(fun j=>t j.succ) := by
      simpa only [gaps,Fin.cons_succ] using ih (fun j=>t j.succ)
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · change boundary T k (times T k (fun j=>gaps T (k+1) t j.succ))-
        gaps T (k+1) t 0=t 0
      rw [ht]
      simp only [gaps,Fin.cons_zero]
      ring
    · simpa only [times,Fin.cons_succ] using congrFun ht j

def gapEquiv (T : ℝ) (k : ℕ) : (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) where
  toFun := gaps T k
  invFun := times T k
  left_inv := times_gaps T k
  right_inv := gaps_times T k
  measurable_toFun := gaps_measurable T k
  measurable_invFun := times_measurable T k

/-- The exact newest-first time-to-gap map preserves product Lebesgue
measure. This uses genuine conditional reflection/translation on each
coordinate, including when the endpoints collide. -/
theorem gaps_measurePreserving (T : ℝ) (k : ℕ) :
    MeasurePreserving (gaps T k) volume volume := by
  induction k with
  | zero =>
    have he : gaps T 0 = id := funext (fun t => Subsingleton.elim _ _)
    rw [he]
    exact MeasurePreserving.id _
  | succ k ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) 0
    have he : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) 0
    have hs : MeasurePreserving
        (fun p : (Fin k → ℝ) × ℝ => (gaps T k p.1,boundary T k p.1-p.2))
        (volume.prod volume) (volume.prod volume) := by
      apply ih.skew_product (g := fun t : Fin k → ℝ => fun u : ℝ => boundary T k t-u)
      · exact ((boundary_measurable T k).comp measurable_fst).sub measurable_snd
      · exact ae_of_all _ (fun t => ((volume : Measure ℝ).measurePreserving_sub_left (boundary T k t)).map_eq)
    have hh := he.symm.comp (Measure.measurePreserving_swap.comp
      (hs.comp (Measure.measurePreserving_swap.comp he)))
    convert! hh using 1
    funext t i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e,gaps,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    all_goals rfl

theorem lintegral_gaps (T : ℝ) (k : ℕ) (F : (Fin k → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, F (gaps T k t))=∫⁻ d, F d :=
  (gaps_measurePreserving T k).lintegral_comp hF

theorem sum_gaps (T : ℝ) (k : ℕ) (t : Fin k → ℝ) :
    (∑ i,gaps T k t i)=T-boundary T k t := by
  induction k with
  | zero => simp [gaps,boundary]
  | succ k ih =>
    rw [gaps,Fin.sum_univ_succ,Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [ih]
    simp only [boundary]
    ring

/-- Strict ordering, with the actual lower endpoint retained. -/
def ordered (q T : ℝ) : (k : ℕ) → (Fin k → ℝ) → Prop
  | 0, _ => q<T
  | k+1, t => q<t 0 ∧ t 0<boundary T k (fun i => t i.succ) ∧
      ordered q T k (fun i => t i.succ)

theorem ordered_iff (q T : ℝ) (k : ℕ) (t : Fin k → ℝ) :
    ordered q T k t ↔ (∀ i,0<gaps T k t i) ∧ (∑ i,gaps T k t i)<T-q := by
  induction k with
  | zero => simp [ordered,gaps]
  | succ k ih =>
    rw [ordered,ih]
    rw [sum_gaps T (k+1) t,sum_gaps T k (fun i => t i.succ)]
    simp only [gaps,Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ]
    simp only [boundary]
    constructor
    · rintro ⟨hq,ht,hg,hb⟩
      exact ⟨⟨by linarith, hg⟩,by linarith⟩
    · rintro ⟨⟨ht,hg⟩,hq⟩
      exact ⟨by linarith,by linarith,hg,by linarith⟩

theorem simplex_measurableSet (k : ℕ) (w : ℝ) :
    MeasurableSet {d : Fin k → ℝ | (∀ i,0<d i) ∧ (∑ i,d i)<w} := by
  have hh := (MeasurableSet.iInter (fun i => measurableSet_lt (f:=fun _ : Fin k → ℝ => (0:ℝ)) measurable_const (measurable_pi_apply i))).inter
    (measurableSet_lt (Finset.measurable_sum Finset.univ
      (fun i _ => (measurable_pi_apply i : Measurable (fun d : Fin k → ℝ => d i))))
      (g:=fun _ : Fin k → ℝ => w) measurable_const)
  convert! hh using 1
  ext d
  simp

/-- Literal ordered time integration equals the positive gap-simplex
integral. No unspecified pushforward or Jacobian premise remains. -/
theorem ordered_lintegral (q T : ℝ) (k : ℕ) (F : (Fin k → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, if ordered q T k t then F (gaps T k t) else 0)=
      ∫⁻ d, if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then F d else 0 := by
  have hm : Measurable (fun d : Fin k → ℝ =>
      if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then F d else 0) :=
    Measurable.ite (simplex_measurableSet k (T-q)) hF measurable_const
  have hh := lintegral_gaps T k _ hm
  simpa only [ordered_iff] using hh

theorem ordered_integral (q T : ℝ) (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    (∫ t, if ordered q T k t then F (gaps T k t) else 0)=
      ∫ d, if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then F d else 0 := by
  have hh := (gaps_measurePreserving T k).integral_comp (gapEquiv T k).measurableEmbedding
    (fun d : Fin k → ℝ => if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then F d else 0)
  simpa only [ordered_iff,gapEquiv] using hh

theorem ordered_integrable_iff (q T : ℝ) (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    Integrable (fun t=>if ordered q T k t then F (gaps T k t) else 0) ↔
      Integrable (fun d=>if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then F d else 0) := by
  have hh := (gaps_measurePreserving T k).integrable_comp_emb (gapEquiv T k).measurableEmbedding
    (g:=fun d : Fin k → ℝ => if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then F d else 0)
  simpa only [Function.comp_def,ordered_iff] using hh

end SHE.OrderedGapCoordinates
