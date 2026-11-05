module

public import SHE.HeatForestComparison
public import SHE.NativeHeatDilation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

/-- Actual native old-age `2a` forests with the terminal age `4a`,
retaining the original ancestor target and center of every finite
cylinder coordinate. The exact periodic dilation factor is paid. -/
theorem integral_two_four_endpoint_le {m k : ℕ} (T : Forest m k)
    (t : Fin (m+k) → ℝ) (ht : TimeCompatible 2 T t) (i : Fin (m+k))
    {q : ℝ} (hq : q < t i) (a : Fin m → HeatCircle) (b : HeatCircle) :
    (∫ x : Fin k → HeatCircle, density T (values a k x)*
      edge (4*(t i-q)) (by have := sub_pos.mpr hq; positivity) (values a k x i) b
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ≤
      (Real.sqrt 2)^k*edge (4*(rootValues k t (rootOf T i)-q))
        (by have hh := elapsed_pos (κ := 2) (by norm_num) T t ht i hq; linarith)
        (a (rootOf T i)) b := by
  have hd : ∀ (r : ℝ) (hr : 0 < r) (a b : HeatCircle),
      edge r hr a b ≤ Real.sqrt 2*edge (2*r) (by positivity) a b := by
    intro r hr a b
    simpa only [NativeHeatAction.edge] using NativeHeatSpan.kernel_double_bound hr a b
  have hh := integral_mixed_endpoint_le (s := 2) (by norm_num) (Real.sqrt_nonneg 2) hd T i
    (r := 4*(t i-q)) (by have := sub_pos.mpr hq; positivity) a b
  simp only [age_eq_elapsed T t ht] at hh
  convert! hh using 1
  congr 2
  ring

end SHE.OrderedHeatForests
