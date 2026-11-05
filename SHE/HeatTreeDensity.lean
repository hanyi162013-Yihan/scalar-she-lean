module

public import SHE.TimedHeatTrees
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.OrderedHeatTrees
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

def density : {n : ℕ} → Tree n → (Fin (n+1) → HeatCircle) → ℝ
  | _,.root,_ => 1
  | _,.branch T parent gap hg,z =>
      density T (fun i => z i.castSucc)*edge gap hg (z parent.castSucc) (z (Fin.last _))

theorem density_nonneg {n : ℕ} (T : Tree n) (z : Fin (n+1) → HeatCircle) : 0 ≤ density T z := by
  induction T with
  | root => exact zero_le_one
  | branch T parent gap hg ih =>
    exact mul_nonneg (ih _) (by unfold NativeHeatAction.edge; exact norm_nonneg _)

theorem density_continuous {n : ℕ} (T : Tree n) : Continuous (density T) := by
  induction T with
  | root => exact continuous_const
  | @branch n T parent gap hg ih =>
    have hp : Continuous (fun z : Fin (n+2) → HeatCircle => fun i : Fin (n+1) => z i.castSucc) := by
      fun_prop
    have hpair : Continuous (fun z : Fin (n+2) → HeatCircle =>
        (z parent.castSucc,z (Fin.last (n+1)))) :=
      (continuous_apply parent.castSucc).prodMk (continuous_apply (Fin.last (n+1)))
    have he : Continuous (fun z : Fin (n+2) → HeatCircle =>
        edge gap hg (z parent.castSucc) (z (Fin.last (n+1)))) :=
      (continuous_edge hg).comp hpair
    exact (ih.comp hp).mul he

theorem density_integrable {n : ℕ} (T : Tree n) (F : (Fin (n+1) → HeatCircle) → ℝ)
    (hF : Measurable F) {B : ℝ} (hb : ∀ z,|F z| ≤ B) (a : HeatCircle) :
    Integrable (fun x : Fin n → HeatCircle => density T (Fin.cons a x)*F (Fin.cons a x))
      (Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle)) := by
  have hp : Continuous (fun x : Fin n → HeatCircle => (Fin.cons a x : Fin (n+1) → HeatCircle)) := by
    fun_prop
  exact ((density_continuous T).comp hp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) |>.mul_bdd (hF.comp hp.measurable).aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb (Fin.cons a x)))

theorem leaf_average_measurable {n : ℕ} (parent : Fin (n+1)) {gap : ℝ} (hg : 0 < gap)
    (F : (Fin (n+2) → HeatCircle) → ℝ) (hF : Measurable F) :
    Measurable (fun z : Fin (n+1) → HeatCircle =>
      action gap hg (fun y => F (Fin.snoc z y)) (z parent)) := by
  have hsnoc : Measurable (fun p : (Fin (n+1) → HeatCircle) × HeatCircle =>
      (Fin.snoc p.1 p.2 : Fin (n+2) → HeatCircle)) := by
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (Prod.snd : (Fin (n+1) → HeatCircle) × HeatCircle → HeatCircle))
    · simpa only [Fin.snoc_castSucc,Function.comp_def] using ((measurable_pi_apply j).comp
        (measurable_fst : Measurable (Prod.fst : (Fin (n+1) → HeatCircle) × HeatCircle → (Fin (n+1) → HeatCircle))))
  have hp : Measurable (fun p : (Fin (n+1) → HeatCircle) × HeatCircle => (p.1 parent,p.2)) :=
    ((measurable_pi_apply parent).comp measurable_fst).prodMk measurable_snd
  have hk : Measurable (fun p : (Fin (n+1) → HeatCircle) × HeatCircle => edge gap hg (p.1 parent) p.2) := by
    simpa only [Function.comp_def] using (continuous_edge hg).measurable.comp hp
  exact (hk.mul (hF.comp hsnoc)).stronglyMeasurable.integral_prod_right.measurable

theorem average_measurable {n : ℕ} (T : Tree n) (F : (Fin (n+1) → HeatCircle) → ℝ)
    (hF : Measurable F) : Measurable (average T F) := by
  induction T with
  | root => exact hF.comp (by fun_prop)
  | branch T parent gap hg ih => exact ih _ (leaf_average_measurable parent hg F hF)

theorem average_abs_bound {n : ℕ} (T : Tree n) (F : (Fin (n+1) → HeatCircle) → ℝ)
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z,|F z| ≤ B) (a : HeatCircle) :
    |average T F a| ≤ B := by
  induction T with
  | root => exact hb _
  | branch T parent gap hg ih =>
    exact ih _ (leaf_average_measurable parent hg F hF) (fun z =>
      action_abs_bound hg (hF.comp (by fun_prop)) hB (fun y => hb (Fin.snoc z y)) (z parent))

end SHE.OrderedHeatTrees
