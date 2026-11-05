module

public import SHE.OrderedHeatForests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

theorem values_continuous {m : ℕ} (a : Fin m → HeatCircle) (k : ℕ) :
    Continuous (values a k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    have hp : Continuous (fun x : Fin (k+1) → HeatCircle => fun j : Fin k => x j.succ) := by fun_prop
    have hv := ih.comp hp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [values,Fin.cons_zero] using (continuous_apply 0 : Continuous (fun x : Fin (k+1) → HeatCircle => x 0))
    · simpa only [values,Fin.cons_succ,Function.comp_def] using (continuous_apply j).comp hv

theorem density_continuous {m k : ℕ} (T : Forest m k) : Continuous (density T) := by
  induction T with
  | roots => exact continuous_const
  | @branch k T parent gap hg ih =>
    have hp : Continuous (fun z : Fin (m+k+1) → HeatCircle => fun i : Fin (m+k) => z i.succ) := by fun_prop
    have hpair : Continuous (fun z : Fin (m+k+1) → HeatCircle => (z parent.succ,z 0)) :=
      (continuous_apply parent.succ).prodMk (continuous_apply 0)
    have he : Continuous (fun z : Fin (m+k+1) → HeatCircle => edge gap hg (z parent.succ) (z 0)) := by
      simpa only [Function.comp_def] using (continuous_edge hg).comp hpair
    exact (ih.comp hp).mul he

theorem leaf_average_measurable {m k : ℕ} (parent : Fin (m+k)) {gap : ℝ} (hg : 0 < gap)
    (F : (Fin (m+k+1) → HeatCircle) → ℝ) (hF : Measurable F) :
    Measurable (fun z : Fin (m+k) → HeatCircle =>
      action gap hg (fun y => F (Fin.cons y z)) (z parent)) := by
  have hp : Measurable (fun p : (Fin (m+k) → HeatCircle) × HeatCircle => (p.1 parent,p.2)) :=
    ((measurable_pi_apply parent).comp measurable_fst).prodMk measurable_snd
  have hk : Measurable (fun p : (Fin (m+k) → HeatCircle) × HeatCircle => edge gap hg (p.1 parent) p.2) := by
    simpa only [Function.comp_def] using (continuous_edge hg).measurable.comp hp
  have hc : Measurable (fun p : (Fin (m+k) → HeatCircle) × HeatCircle =>
      (Fin.cons p.2 p.1 : Fin (m+k+1) → HeatCircle)) := by fun_prop
  exact (hk.mul (hF.comp hc)).stronglyMeasurable.integral_prod_right.measurable

theorem density_integrable {m k : ℕ} (T : Forest m k)
    (F : (Fin (m+k) → HeatCircle) → ℝ) (hF : Measurable F) {B : ℝ}
    (hb : ∀ z, |F z| ≤ B) (a : Fin m → HeatCircle) :
    Integrable (fun x : Fin k → HeatCircle => density T (values a k x)*F (values a k x))
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
  have hp := values_continuous a k
  exact ((density_continuous T).comp hp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) |>.mul_bdd (hF.comp hp.measurable).aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb (values a k x)))

theorem integral_cons {k : ℕ} (G : (Fin (k+1) → HeatCircle) → ℝ)
    (hG : Integrable G (Measure.pi (fun _ : Fin (k+1) => AddCircle.haarAddCircle))) :
    (∫ x, G x ∂Measure.pi (fun _ : Fin (k+1) => AddCircle.haarAddCircle)) =
      ∫ x : Fin k → HeatCircle, ∫ y : HeatCircle, G (Fin.cons y x)
        ∂AddCircle.haarAddCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => HeatCircle) 0).symm
  have hp : MeasurePreserving e
      (AddCircle.haarAddCircle.prod (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)))
      (Measure.pi (fun _ : Fin (k+1) => AddCircle.haarAddCircle)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => AddCircle.haarAddCircle) 0).symm
  have hi : Integrable (fun p : HeatCircle × (Fin k → HeatCircle) => G (Fin.cons p.1 p.2))
      (AddCircle.haarAddCircle.prod (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))) := by
    simpa only [e,Function.comp_def,MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv,Fin.insertNth_zero,Equiv.coe_fn_mk,cast_eq] using hp.integrable_comp_of_integrable hG
  calc
    _ = ∫ p : HeatCircle × (Fin k → HeatCircle), G (Fin.cons p.1 p.2)
        ∂AddCircle.haarAddCircle.prod (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
      rw [← hp.integral_comp']
      simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv,Fin.insertNth_zero,Equiv.coe_fn_mk,cast_eq]
    _ = _ := integral_prod_symm _ hi

/-- The literal full-frame heat forest is an actual finite product Haar
integral. No original root center is integrated out or identified. -/
theorem average_eq_integral {m k : ℕ} (T : Forest m k)
    (F : (Fin (m+k) → HeatCircle) → ℝ) (hF : Measurable F) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ z, |F z| ≤ B) (a : Fin m → HeatCircle) :
    average T F a = ∫ x : Fin k → HeatCircle, density T (values a k x)*F (values a k x)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
  induction T with
  | roots =>
    rw [Measure.pi_of_empty _ (fun i => Fin.elim0 i)]
    simp only [integral_dirac,density,one_mul,average,values]
  | @branch k T parent gap hg ih =>
    let G : (Fin (m+k) → HeatCircle) → ℝ := fun z =>
      action gap hg (fun y => F (Fin.cons y z)) (z parent)
    have hG : Measurable G := leaf_average_measurable parent hg F hF
    have hGb : ∀ z, |G z| ≤ B := fun z =>
      action_abs_bound hg (hF.comp (by fun_prop)) hB (fun y => hb (Fin.cons y z)) (z parent)
    change average T G a = _
    rw [ih G hG hGb,integral_cons _ (density_integrable (.branch T parent gap hg) F hF hb a)]
    apply integral_congr_ae
    filter_upwards [] with x
    change density T (values a k x)*
      (∫ y : HeatCircle, edge gap hg (values a k x parent) y * F (Fin.cons y (values a k x))
        ∂AddCircle.haarAddCircle) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [values_cons,density_cons]
    exact (mul_assoc _ _ _).symm

theorem average_eq_integral_continuous {m k : ℕ} (T : Forest m k)
    (F : (Fin (m+k) → HeatCircle) → ℝ) (hF : Continuous F) (a : Fin m → HeatCircle) :
    average T F a = ∫ x : Fin k → HeatCircle, density T (values a k x)*F (values a k x)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
  obtain ⟨B,hB⟩ := (isCompact_range hF.abs).bddAbove
  exact average_eq_integral T F hF.measurable (B := max 0 B) (le_max_left _ _)
    (fun z => (hB ⟨z,rfl⟩).trans (le_max_right _ _)) a

theorem integral_endpoint_kernel {m k : ℕ} (T : Forest m k) (i : Fin (m+k))
    {r : ℝ} (hr : 0 < r) (a : Fin m → HeatCircle) (b : HeatCircle) :
    (∫ x : Fin k → HeatCircle, density T (values a k x)*edge r hr (values a k x i) b
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
      edge (age T i+r) (add_pos_of_nonneg_of_pos (age_nonneg T i) hr) (a (rootOf T i)) b := by
  have hc : Continuous (fun z : Fin (m+k) → HeatCircle => edge r hr (z i) b) := by
    simpa only [Function.comp_def] using (continuous_edge hr).comp
      ((continuous_apply i : Continuous (fun z : Fin (m+k) → HeatCircle => z i)).prodMk continuous_const)
  rw [← average_eq_integral_continuous T _ hc a]
  exact endpoint_kernel T i hr a b

end SHE.OrderedHeatForests
