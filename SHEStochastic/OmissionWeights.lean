module

public import SHEStochastic.DirectionalAffineProduct
public import SHEStochastic.MatrixJetClosure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.DirectionalJets
open MatrixJetClosure
variable {E : Type*}

theorem omissions_count (w : List E) : (omissions w).length=w.length := by
  induction w with
  | nil => rfl
  | cons v w ih => simp only [omissions, List.length_cons, List.length_map, ih]

theorem omission_length (w : List E) (q : E × List E) (hq : q∈omissions w) :
    q.2.length+1=w.length := by
  induction w generalizing q with
  | nil => simp only [omissions, List.not_mem_nil] at hq
  | cons v w ih =>
    simp only [omissions, List.mem_cons, List.mem_map] at hq
    rcases hq with rfl | ⟨r, hr, rfl⟩
    · rfl
    · simpa only [List.length_cons] using congrArg (fun n : ℕ => n+1) (ih r hr)

theorem omission_sublist (w : List E) (q : E × List E) (hq : q∈omissions w) :
    q.2.Sublist w := by
  induction w generalizing q with
  | nil => simp only [omissions, List.not_mem_nil] at hq
  | cons v w ih =>
    simp only [omissions, List.mem_cons, List.mem_map] at hq
    rcases hq with rfl | ⟨r, hr, rfl⟩
    · exact List.Sublist.cons _ (List.Sublist.refl _)
    · exact List.Sublist.cons_cons _ (ih r hr)

theorem omission_mem (w : List E) (q : E × List E) (hq : q∈omissions w) : q.1∈w := by
  induction w generalizing q with
  | nil => simp only [omissions, List.not_mem_nil] at hq
  | cons v w ih =>
    simp only [omissions, List.mem_cons, List.mem_map] at hq
    rcases hq with rfl | ⟨r, hr, rfl⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih r hr)

/-- The omitted-direction product identity retains multiplicities and
does not divide by a direction norm, so zero directions cause no gap. -/
theorem omission_product (w : List E) (ρ : E → ℝ) (q : E × List E) (hq : q∈omissions w) :
    ρ q.1*weight ρ q.2=weight ρ w := by
  induction w generalizing q with
  | nil => simp only [omissions, List.not_mem_nil] at hq
  | cons v w ih =>
    simp only [omissions, List.mem_cons, List.mem_map] at hq
    rcases hq with rfl | ⟨r, hr, rfl⟩
    · rfl
    · change ρ r.1*(ρ v*weight ρ r.2)=ρ v*weight ρ w
      rw [← ih r hr]
      ring

theorem weight_le_scaled [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ B : E → ℝ) (hρ : ∀ v, 0 ≤ ρ v) (hB : ∀ v, 0 ≤ B v)
    (K : ℝ) (hK : 0 ≤ K) (w : List E) (h : ∀ v∈w, ρ v ≤ K*B v) :
    weight ρ w ≤ K^w.length*weight B w := by
  induction w with
  | nil => simp [weight]
  | cons v w ih =>
    have hh := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    change ρ v*weight ρ w ≤ K^(w.length+1)*(B v*weight B w)
    calc
      _ ≤ (K*B v)*(K^w.length*weight B w) :=
        mul_le_mul (h v List.mem_cons_self) hh (weight_nonneg ρ hρ w) (mul_nonneg hK (hB v))
      _ = _ := by rw [pow_succ]; ring

end SHEStochastic.DirectionalJets
