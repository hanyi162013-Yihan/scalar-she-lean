module

public import SHE.TimedHeatForests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

def scale {m : ℕ} (s : ℝ) (hs : 0 < s) : {k : ℕ} → Forest m k → Forest m k
  | _,.roots => .roots
  | _,.branch T parent gap hg => .branch (scale s hs T) parent (s*gap) (mul_pos hs hg)

theorem rootOf_scale {m k : ℕ} (s : ℝ) (hs : 0 < s) (T : Forest m k) :
    rootOf (scale s hs T) = rootOf T := by
  induction T with
  | roots => rfl
  | branch T parent gap hg ih => simp only [scale,rootOf,ih]

theorem age_scale {m k : ℕ} (s : ℝ) (hs : 0 < s) (T : Forest m k) (i : Fin (m+k)) :
    age (scale s hs T) i=s*age T i := by
  induction T with
  | roots => simp only [scale,age,mul_zero]
  | branch T parent gap hg ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [scale,age,Fin.cons_zero]
      rw [ih]
      ring
    · simpa only [scale,age,Fin.cons_succ] using ih j

theorem density_le_scale {m k : ℕ} {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (he : ∀ (r : ℝ) (hr : 0 < r) (a b : HeatCircle),
      edge r hr a b ≤ C*edge (s*r) (mul_pos hs hr) a b)
    (T : Forest m k) (z : Fin (m+k) → HeatCircle) :
    density T z ≤ C^k*density (scale s hs T) z := by
  induction T with
  | roots => simp only [scale,density,pow_zero,one_mul,le_refl]
  | @branch k T parent gap hg ih =>
    simp only [scale,density]
    have hp := ih (fun i => z i.succ)
    have hh := he gap hg (z parent.succ) (z 0)
    have hn : 0 ≤ edge gap hg (z parent.succ) (z 0) := by
      unfold NativeHeatAction.edge
      exact norm_nonneg _
    calc
      _ ≤ (C^k*density (scale s hs T) (fun i => z i.succ))*
          (C*edge (s*gap) (mul_pos hs hg) (z parent.succ) (z 0)) :=
        mul_le_mul hp hh hn (mul_nonneg (pow_nonneg hC _) (density_nonneg _ _))
      _ = _ := by rw [pow_succ]; ring

/-- Actual full-frame spatial integration with different old/terminal
heat dilations. All root locations and the selected ancestor are kept. -/
theorem integral_mixed_endpoint_le {m k : ℕ} {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (he : ∀ (r : ℝ) (hr : 0 < r) (a b : HeatCircle),
      edge r hr a b ≤ C*edge (s*r) (mul_pos hs hr) a b)
    (T : Forest m k) (i : Fin (m+k)) {r : ℝ} (hr : 0 < r)
    (a : Fin m → HeatCircle) (b : HeatCircle) :
    (∫ x : Fin k → HeatCircle, density T (values a k x)*edge r hr (values a k x i) b
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ≤
      C^k*edge (s*age T i+r)
        (add_pos_of_nonneg_of_pos (mul_nonneg hs.le (age_nonneg T i)) hr)
        (a (rootOf T i)) b := by
  have hc : Continuous (fun z : Fin (m+k) → HeatCircle => edge r hr (z i) b) := by
    simpa only [Function.comp_def] using (continuous_edge hr).comp
      ((continuous_apply i : Continuous (fun z : Fin (m+k) → HeatCircle => z i)).prodMk continuous_const)
  have hi (T' : Forest m k) : Integrable (fun x : Fin k → HeatCircle =>
      density T' (values a k x)*edge r hr (values a k x i) b)
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) :=
    (((density_continuous T').mul hc).comp (values_continuous a k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x : Fin k → HeatCircle, C^k*(density (scale s hs T) (values a k x)*
        edge r hr (values a k x i) b)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
      apply integral_mono (hi T) ((hi (scale s hs T)).const_mul _)
      intro x
      have hn : 0 ≤ edge r hr (values a k x i) b := by
        unfold NativeHeatAction.edge
        exact norm_nonneg _
      exact (mul_le_mul_of_nonneg_right (density_le_scale hs hC he T _) hn).trans_eq (by ring)
    _ = _ := by
      rw [integral_const_mul,integral_endpoint_kernel]
      simp only [age_scale,rootOf_scale]

end SHE.OrderedHeatForests
