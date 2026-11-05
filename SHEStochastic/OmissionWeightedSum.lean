module

public import SHEStochastic.OmissionWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.DirectionalJets
open MatrixJetClosure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Removing any one direction preserves the full norm product after
multiplying by the removed norm. The estimate stays valid at zero. -/
theorem omission_weight_bound (ρ B : E → ℝ) (hρ : ∀ v, 0 ≤ ρ v) (hB : ∀ v, 0 ≤ B v)
    (w : List E) (h : ∀ v∈w, ρ v ≤ 2*B v) (q : E × List E) (hq : q∈omissions w) :
    B q.1*weight ρ q.2 ≤ (2 : ℝ)^w.length*weight B w := by
  have hs := omission_sublist w q hq
  have hp := weight_le_scaled ρ B hρ hB 2 (by norm_num) q.2
    (fun v hv => h v (hs.subset hv))
  have hLen := omission_length w q hq
  have hPow : (2 : ℝ)^q.2.length ≤ (2 : ℝ)^w.length := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ B q.1*((2 : ℝ)^q.2.length*weight B q.2) := mul_le_mul_of_nonneg_left hp (hB q.1)
    _ = (2 : ℝ)^q.2.length*(B q.1*weight B q.2) := by ring
    _ = (2 : ℝ)^q.2.length*weight B w := by rw [omission_product w B q hq]
    _ ≤ _ := mul_le_mul_of_nonneg_right hPow (weight_nonneg B hB w)

/-- The whole affine-numerator sum costs only the fixed derivative
order. No number of spatial cells enters this combinatorial bound. -/
theorem omission_sum_bound (ρ B : E → ℝ) (hρ : ∀ v, 0 ≤ ρ v) (hB : ∀ v, 0 ≤ B v)
    (w : List E) (h : ∀ v∈w, ρ v ≤ 2*B v) :
    ((omissions w).map (fun q => B q.1*weight ρ q.2)).sum ≤
      (w.length : ℝ)*(2 : ℝ)^w.length*weight B w := by
  calc
    _ ≤ ((omissions w).map (fun _ => (2 : ℝ)^w.length*weight B w)).sum :=
      MatrixFrobeniusNorm.sum_map_le (omissions w) _ _
        (fun q hq => omission_weight_bound ρ B hρ hB w h q hq)
    _ = _ := by simp [List.map_const', nsmul_eq_mul, omissions_count, mul_assoc]

end SHEStochastic.DirectionalJets
