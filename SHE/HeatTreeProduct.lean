module

public import SHE.HeatTreeDensity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.OrderedHeatTrees
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

/-- Fubini with the newest spatial vertex in the last coordinate. -/
theorem integral_snoc {n : ℕ} (G : (Fin (n+1) → HeatCircle) → ℝ)
    (hG : Integrable G (Measure.pi (fun _ : Fin (n+1) => AddCircle.haarAddCircle))) :
    (∫ x, G x ∂Measure.pi (fun _ : Fin (n+1) => AddCircle.haarAddCircle)) =
      ∫ x : Fin n → HeatCircle, ∫ y : HeatCircle, G (Fin.snoc x y)
        ∂AddCircle.haarAddCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => HeatCircle) (Fin.last n)).symm
  have hp : MeasurePreserving e
      (AddCircle.haarAddCircle.prod (Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle)))
      (Measure.pi (fun _ : Fin (n+1) => AddCircle.haarAddCircle)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => AddCircle.haarAddCircle) (Fin.last n)).symm
  have hi : Integrable (fun p : HeatCircle × (Fin n → HeatCircle) => G (Fin.snoc p.2 p.1))
      (AddCircle.haarAddCircle.prod (Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle))) := by
    simpa only [e,Function.comp_def,MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv,Fin.insertNth_last',Equiv.coe_fn_mk] using hp.integrable_comp_of_integrable hG
  calc
    _ = ∫ p : HeatCircle × (Fin n → HeatCircle), G (Fin.snoc p.2 p.1)
        ∂AddCircle.haarAddCircle.prod (Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle)) := by
      rw [← hp.integral_comp']
      simp only [e,Function.comp_def,MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv,Fin.insertNth_last',Equiv.coe_fn_mk]
    _ = _ := integral_prod_symm _ hi

theorem density_snoc {n : ℕ} (T : Tree n) (parent : Fin (n+1)) {gap : ℝ} (hg : 0 < gap)
    (z : Fin (n+1) → HeatCircle) (y : HeatCircle) :
    density (.branch T parent gap hg) (Fin.snoc z y) =
      density T z * edge gap hg (z parent) y := by
  simp only [density,Fin.snoc_castSucc,Fin.snoc_last]

/-- The recursive heat-tree average is exactly the finite spatial product
integral of the original positive edge kernels. -/
theorem average_eq_integral {n : ℕ} (T : Tree n) (F : (Fin (n+1) → HeatCircle) → ℝ)
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |F z| ≤ B) (a : HeatCircle) :
    average T F a = ∫ x : Fin n → HeatCircle,
      density T (Fin.cons a x)*F (Fin.cons a x)
      ∂Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle) := by
  induction T with
  | root =>
    rw [Measure.pi_of_empty _ (fun i => Fin.elim0 i)]
    simp only [integral_dirac,density,one_mul,average]
    congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  | @branch n T parent gap hg ih =>
    let G : (Fin (n+1) → HeatCircle) → ℝ := fun z =>
      action gap hg (fun y => F (Fin.snoc z y)) (z parent)
    have hG : Measurable G := leaf_average_measurable parent hg F hF
    have hGb : ∀ z, |G z| ≤ B := fun z =>
      action_abs_bound hg (hF.comp (by fun_prop)) hB (fun y => hb (Fin.snoc z y)) (z parent)
    change average T G a = _
    rw [ih G hG hGb,integral_snoc _ (density_integrable (.branch T parent gap hg) F hF hb a)]
    apply integral_congr_ae
    filter_upwards [] with x
    change density T (Fin.cons a x) *
      (∫ y : HeatCircle, edge gap hg ((Fin.cons a x : Fin (n+1) → HeatCircle) parent) y * F (Fin.snoc (Fin.cons a x) y)
        ∂AddCircle.haarAddCircle) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [Fin.cons_snoc_eq_snoc_cons,density_snoc]
    exact (mul_assoc _ _ _).symm

end SHE.OrderedHeatTrees
