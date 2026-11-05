module

public import SHEStochastic.OmissionWeightedSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.AffineOneInputBound
open DirectionalJets MatrixJetClosure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def expression (C : ℕ → ℝ) (ρ R : E → ℝ) (s a : ℝ) (w : List E) : ℝ :=
  (s⁻¹*C w.length*weight ρ w)*a+
    ((omissions w).map (fun q => (s⁻¹*C q.2.length*weight ρ q.2)*R q.1)).sum

/-- The scalar bookkeeping of an affine physical column: one input
uses its local `L²` norm, every other input uses its own bounded norm.
Zero bounded directions are covered without normalization or division. -/
theorem one_input (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (ρ R B : E → ℝ)
    (hρ : ∀ v, 0 ≤ ρ v) (hB : ∀ v, 0 ≤ B v)
    (s : ℝ) (hs : 0 < s) (a A β : ℝ) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (ha : a ≤ A*s) (v : E) (hv : R v ≤ β) (hρv : ρ v ≤ s⁻¹*β)
    (w : List E) (hw : ∀ q∈w, ρ q ≤ 2*B q ∧ R q ≤ B q*s) :
    expression C ρ R s a (v::w) ≤
      s⁻¹*((2 : ℝ)^w.length*(A*C (w.length+1)+((w.length : ℝ)+1)*C w.length))*β*weight B w := by
  let r := s⁻¹
  let P := (2 : ℝ)^w.length*weight B w
  have hr : 0 ≤ r := inv_nonneg.mpr hs.le
  have hrs : r*s=1 := inv_mul_cancel₀ hs.ne'
  have hP : 0 ≤ P := mul_nonneg (by positivity) (weight_nonneg B hB w)
  have hp : weight ρ w ≤ P := weight_le_scaled ρ B hρ hB 2 (by norm_num) w (fun q hq => (hw q hq).1)
  have hMain : (r*C (w.length+1)*(ρ v*weight ρ w))*a ≤ r*(A*C (w.length+1))*β*P := by
    calc
      _ ≤ (r*C (w.length+1)*(ρ v*weight ρ w))*(A*s) :=
        mul_le_mul_of_nonneg_left ha (mul_nonneg (mul_nonneg hr (hC _))
          (mul_nonneg (hρ _) (weight_nonneg ρ hρ w)))
      _ = (r*s)*(A*C (w.length+1)*(ρ v*weight ρ w)) := by ring
      _ = A*C (w.length+1)*(ρ v*weight ρ w) := by rw [hrs, one_mul]
      _ ≤ A*C (w.length+1)*((r*β)*P) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hρv hp (weight_nonneg ρ hρ w) (mul_nonneg hr hβ))
          (mul_nonneg hA (hC _))
      _ = _ := by ring
  have hHead : (r*C w.length*weight ρ w)*R v ≤ r*C w.length*β*P := by
    calc
      _ ≤ (r*C w.length*weight ρ w)*β :=
        mul_le_mul_of_nonneg_left hv (mul_nonneg (mul_nonneg hr (hC _)) (weight_nonneg ρ hρ w))
      _ = (r*C w.length*β)*weight ρ w := by ring
      _ ≤ (r*C w.length*β)*P := mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hr (hC _)) hβ)
      _ = _ := by ring
  have hRest : ((omissions w).map (fun q =>
      (r*C (q.2.length+1)*(ρ v*weight ρ q.2))*R q.1)).sum ≤
      (w.length : ℝ)*(r*C w.length*β*P) := by
    calc
      _ ≤ ((omissions w).map (fun _ => r*C w.length*β*P)).sum := by
        apply MatrixFrobeniusNorm.sum_map_le
        intro q hq
        have hLen := omission_length w q hq
        have hRv := (hw q.1 (omission_mem w q hq)).2
        have hqP : B q.1*weight ρ q.2 ≤ P :=
          omission_weight_bound ρ B hρ hB w (fun u hu => (hw u hu).1) q hq
        rw [hLen]
        calc
          _ ≤ (r*C w.length*(ρ v*weight ρ q.2))*(B q.1*s) :=
            mul_le_mul_of_nonneg_left hRv (mul_nonneg (mul_nonneg hr (hC _))
              (mul_nonneg (hρ _) (weight_nonneg ρ hρ q.2)))
          _ = (r*s)*(C w.length*(ρ v*(B q.1*weight ρ q.2))) := by ring
          _ = C w.length*(ρ v*(B q.1*weight ρ q.2)) := by rw [hrs, one_mul]
          _ ≤ C w.length*((r*β)*P) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hρv hqP
              (mul_nonneg (hB _) (weight_nonneg ρ hρ q.2)) (mul_nonneg hr hβ)) (hC _)
          _ = _ := by ring
      _ = _ := by simp [List.map_const', nsmul_eq_mul, omissions_count]
  have he : expression C ρ R s a (v::w)=
      (r*C (w.length+1)*(ρ v*weight ρ w))*a+(r*C w.length*weight ρ w)*R v+
      ((omissions w).map (fun q => (r*C (q.2.length+1)*(ρ v*weight ρ q.2))*R q.1)).sum := by
    simp only [expression, omissions, List.length_cons, List.map_cons, List.sum_cons,
      List.map_map, Function.comp_def]
    change _=(_+_)+_
    simp only [weight, List.map_cons, List.prod_cons, r]
    ring
  rw [he]
  apply (add_le_add (add_le_add hMain hHead) hRest).trans_eq
  dsimp only [P, r]
  ring

end SHEStochastic.AffineOneInputBound
