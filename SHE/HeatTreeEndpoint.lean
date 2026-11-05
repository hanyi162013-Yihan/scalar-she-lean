module

public import SHE.HeatTreeProduct

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.OrderedHeatTrees
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

theorem average_eq_integral_continuous {n : ℕ} (T : Tree n)
    (F : (Fin (n+1) → HeatCircle) → ℝ) (hF : Continuous F) (a : HeatCircle) :
    average T F a = ∫ x : Fin n → HeatCircle,
      density T (Fin.cons a x)*F (Fin.cons a x)
      ∂Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle) := by
  obtain ⟨B,hB⟩ := (isCompact_range hF.abs).bddAbove
  exact average_eq_integral T F hF.measurable (B := max 0 B) (le_max_left _ _)
    (fun z => (hB ⟨z,rfl⟩).trans (le_max_right _ _)) a

/-- Every finite heat-tree density has total spatial mass one. -/
theorem density_mass {n : ℕ} (T : Tree n) (a : HeatCircle) :
    (∫ x : Fin n → HeatCircle, density T (Fin.cons a x)
      ∂Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle)) = 1 := by
  have hh := average_eq_integral_continuous T (fun _ => (1 : ℝ)) continuous_const a
  simpa only [mul_one,average_const] using hh.symm

/-- Literal product-space spatial integration for an arbitrary selected
terminal vertex; all off-path branches integrate to one. -/
theorem integral_endpoint_kernel {n : ℕ} (T : Tree n) (i : Fin (n+1))
    {r : ℝ} (hr : 0 < r) (a b : HeatCircle) :
    (∫ x : Fin n → HeatCircle, density T (Fin.cons a x)*
      edge r hr ((Fin.cons a x : Fin (n+1) → HeatCircle) i) b
      ∂Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle)) =
      edge (age T i+r) (add_pos_of_nonneg_of_pos (age_nonneg T i) hr) a b := by
  have hF : Continuous (fun z : Fin (n+1) → HeatCircle => edge r hr (z i) b) := by
    simpa only [Function.comp_def] using (continuous_edge hr).comp
      ((continuous_apply i : Continuous (fun z : Fin (n+1) → HeatCircle => z i)).prodMk continuous_const)
  rw [← average_eq_integral_continuous T
    (fun z => edge r hr (z i) b) hF a]
  exact endpoint_kernel T i hr a b

/-- The original strictly ordered physical times telescope inside the
actual finite product Haar integral, for every earlier-parent assignment. -/
theorem integral_timed_endpoint_kernel (κ : ℝ) (hκ : 0 < κ) (n : ℕ)
    (t : Fin (n+1) → ℝ) (ht : StrictAnti t)
    (parent : (j : Fin n) → Fin (j.val+1)) (i : Fin (n+1))
    {q : ℝ} (hq : q < t i) (a b : HeatCircle) :
    (∫ x : Fin n → HeatCircle, density (ofTimes κ hκ n t ht parent) (Fin.cons a x)*
      edge (κ*(t i-q)) (mul_pos hκ (sub_pos.mpr hq))
        ((Fin.cons a x : Fin (n+1) → HeatCircle) i) b
      ∂Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle)) =
      edge (κ*(t 0-q)) (by
        have hi : t i ≤ t 0 := ht.antitone (Fin.zero_le i)
        exact mul_pos hκ (by linarith)) a b := by
  have hF : Continuous (fun z : Fin (n+1) → HeatCircle =>
      edge (κ*(t i-q)) (mul_pos hκ (sub_pos.mpr hq)) (z i) b) := by
    simpa only [Function.comp_def] using (continuous_edge (mul_pos hκ (sub_pos.mpr hq))).comp
      ((continuous_apply i : Continuous (fun z : Fin (n+1) → HeatCircle => z i)).prodMk continuous_const)
  rw [← average_eq_integral_continuous _ _ hF a]
  exact timed_endpoint_kernel κ hκ n t ht parent i hq a b

end SHE.OrderedHeatTrees
