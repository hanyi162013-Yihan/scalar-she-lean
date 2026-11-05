module

public import SHE.ParentHeatForests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory StoppedFourier NativeHeatAction
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

/-- The actual product of all earlier-parent heat sums integrates to a
finite sum of the original root kernels. Old `2a` and terminal `4a` ages,
all original root targets, and all original root centers are retained. -/
theorem parent_integral_two_four_le {m : ℕ} (k : ℕ) (t : Fin (m+k) → ℝ)
    (ht : OrderedTimes k t) (i : Fin (m+k)) {q : ℝ} (hq : ∀ j, q < t j)
    (a : Fin m → HeatCircle) (b : HeatCircle) :
    (∫ x : Fin k → HeatCircle, parentDensity 2 (by norm_num) k t ht (values a k x)*
      edge (4*(t i-q)) (by have := sub_pos.mpr (hq i); positivity) (values a k x i) b
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ≤
      (Fintype.card (Choices m k) : ℝ)*(Real.sqrt 2)^k*
        ∑ j : Fin m, edge (4*(rootValues k t j-q))
          (by have := sub_pos.mpr (rootValues_lt t hq j); positivity) (a j) b := by
  let T : Choices m k → Forest m k := ofChoices 2 (by norm_num) k t ht
  have hc : Continuous (fun z : Fin (m+k) → HeatCircle =>
      edge (4*(t i-q)) (by have := sub_pos.mpr (hq i); positivity) (z i) b) := by
    simpa only [Function.comp_def] using
      (continuous_edge (by have := sub_pos.mpr (hq i); positivity : 0 < 4*(t i-q))).comp
        ((continuous_apply i : Continuous (fun z : Fin (m+k) → HeatCircle => z i)).prodMk continuous_const)
  have hInt (Q : Choices m k) : Integrable (fun x : Fin k → HeatCircle =>
      density (T Q) (values a k x)*
        edge (4*(t i-q)) (by have := sub_pos.mpr (hq i); positivity) (values a k x i) b)
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) :=
    (((density_continuous _).mul hc).comp (values_continuous a k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum (Q : Choices m k) :
      edge (4*(rootValues k t (rootOf (T Q) i)-q))
        (by have := sub_pos.mpr (rootValues_lt t hq (rootOf (T Q) i)); positivity)
        (a (rootOf (T Q) i)) b ≤
      ∑ j : Fin m, edge (4*(rootValues k t j-q))
        (by have := sub_pos.mpr (rootValues_lt t hq j); positivity) (a j) b := by
    exact Finset.single_le_sum (f := fun j : Fin m => edge (4*(rootValues k t j-q))
      (by have := sub_pos.mpr (rootValues_lt t hq j); positivity) (a j) b)
      (fun j _ => by unfold NativeHeatAction.edge; exact norm_nonneg _)
      (Finset.mem_univ _)
  calc
    _ = ∑ Q : Choices m k, ∫ x : Fin k → HeatCircle, density (T Q) (values a k x)*
        edge (4*(t i-q)) (by have := sub_pos.mpr (hq i); positivity) (values a k x i) b
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
      simp_rw [← sum_density_eq 2 (by norm_num) k t ht,Finset.sum_mul]
      exact integral_finset_sum _ (fun Q _ => hInt Q)
    _ ≤ ∑ _Q : Choices m k, (Real.sqrt 2)^k*
        ∑ j : Fin m, edge (4*(rootValues k t j-q))
          (by have := sub_pos.mpr (rootValues_lt t hq j); positivity) (a j) b := by
      apply Finset.sum_le_sum
      intro Q _
      exact (integral_two_four_endpoint_le (T Q) t
        (ofChoices_compatible 2 (by norm_num) k t ht Q) i (hq i) a b).trans
          (mul_le_mul_of_nonneg_left (hsum Q) (pow_nonneg (Real.sqrt_nonneg 2) k))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end SHE.OrderedHeatForests
