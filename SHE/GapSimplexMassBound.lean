module

public import SHE.GapSimplexFaces

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.GapSimplexFaces
open Set MeasureTheory
open scoped BigOperators
open Classical
variable {k : ℕ}

theorem mul_prod_update (M : Fin k→ℝ) (i : Fin k) (a : ℝ) :
    M i*(∏ j,Function.update M i a j)=a*(∏ j,M j) := by
  rw [←Finset.mul_prod_erase Finset.univ (Function.update M i a) (Finset.mem_univ i),
    ←Finset.mul_prod_erase Finset.univ M (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : (∏ j∈Finset.univ.erase i,Function.update M i a j)=∏ j∈Finset.univ.erase i,M j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  rw [he]
  ring

/-- A largest-gap cap expressed through the true one-dimensional masses
gives a symmetric simplex bound. The square of the finite number of
gaps is the only combinatorial cost. -/
theorem density_mass_bound {w : ℝ} (hw : 0<w) (F : Fin (k+1)→ℝ→ℝ)
    (hm : ∀ i,Measurable (F i)) (hF : ∀ i t,0<t→0≤F i t)
    (hi : ∀ i,Integrable (cut w (F i))) (M : Fin (k+1)→ℝ) (hM : ∀ i,0≤M i)
    (hmass : ∀ i,(∫ t,cut w (F i) t)=M i)
    (hcap : ∀ i t,w/((k+1:ℕ):ℝ)≤t→t≤w→F i t≤((k+1:ℕ):ℝ)/w*M i) :
    Integrable (density w F) ∧
      (∫ d,density w F d)≤((k+1:ℕ):ℝ)^2/w*(∏ i,M i) := by
  let A : Fin (k+1)→ℝ := fun i=>((k+1:ℕ):ℝ)/w*M i
  have hh := density_integral_bound hw F hm hF hi A
    (fun i=>mul_nonneg (div_nonneg (by positivity) hw.le) (hM i)) hcap
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hface (i : Fin (k+1)) :
      A i*(∫ d,face w F i d)=((k+1:ℕ):ℝ)/w*(∏ i,M i) := by
    refine Fin.cases ?_ (fun j=>?_) i
    · rw [face_integral,Fin.cases_zero]
      simp_rw [hmass]
      rw [Fin.prod_univ_succ]
      dsimp only [A]
      ring
    · rw [face_integral,Fin.cases_succ]
      have he : (∏ l : Fin k,∫ t,cut w (Function.update (fun l=>F l.succ) j (F 0) l) t)=
          ∏ l,Function.update (fun l=>M l.succ) j (M 0) l := by
        apply Finset.prod_congr rfl
        intro l _
        by_cases hl : l=j
        · subst l
          simp only [Function.update_self]
          exact hmass 0
        · simp only [Function.update_of_ne hl]
          exact hmass l.succ
      rw [he,Fin.prod_univ_succ]
      dsimp only [A]
      calc
        _ = (((k+1:ℕ):ℝ)/w)*
            (M j.succ*(∏ l,Function.update (fun l=>M l.succ) j (M 0) l)) := by ring
        _ = _ := by
          exact congrArg (fun z : ℝ=>(((k+1:ℕ):ℝ)/w)*z)
            (mul_prod_update (fun l=>M l.succ) j (M 0))
  simp_rw [hface]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end SHE.GapSimplexFaces
