module

public import SHE.OrderedGapCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.GapSimplexReflection
open Set MeasureTheory
open scoped BigOperators
open Classical
variable {k : ℕ}

def slack (w : ℝ) (d : Fin k → ℝ) : ℝ := w-∑ j,d j

def swap (w : ℝ) (i : Fin k) (d : Fin k → ℝ) : Fin k → ℝ :=
  Function.update d i (slack w d)

theorem swap_same (w : ℝ) (i : Fin k) (d : Fin k → ℝ) : swap w i d i=slack w d := by
  simp [swap]

theorem swap_other (w : ℝ) (i j : Fin k) (hij : j≠i) (d : Fin k → ℝ) : swap w i d j=d j := by
  simp [swap,Function.update_of_ne hij]

theorem sum_swap (w : ℝ) (i : Fin k) (d : Fin k → ℝ) :
    (∑ j,swap w i d j)=w-d i := by
  rw [swap,Finset.sum_update_of_mem (Finset.mem_univ i)]
  dsimp only [slack]
  have hh := Finset.sum_erase_add Finset.univ d (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  linarith

theorem slack_swap (w : ℝ) (i : Fin k) (d : Fin k → ℝ) : slack w (swap w i d)=d i := by
  rw [slack,sum_swap]
  ring

theorem swap_involutive (w : ℝ) (i : Fin k) : Function.Involutive (swap w i) := by
  intro d
  funext j
  by_cases hj : j=i
  · subst j
    rw [swap_same,slack_swap]
  · rw [swap_other w i j hj,swap_other w i j hj]

theorem slack_measurable (w : ℝ) : Measurable (slack w : (Fin k → ℝ) → ℝ) := by
  exact measurable_const.sub (Finset.measurable_sum _ (fun j _=>measurable_pi_apply j))

theorem swap_measurable (w : ℝ) (i : Fin k) : Measurable (swap w i) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j=i
  · subst j
    simpa only [swap_same] using slack_measurable (k:=k) w
  · simpa only [swap_other w i j hj] using (measurable_pi_apply j : Measurable (fun d : Fin k → ℝ=>d j))

def swapEquiv (w : ℝ) (i : Fin k) : (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) where
  toFun := swap w i
  invFun := swap w i
  left_inv := swap_involutive w i
  right_inv := swap_involutive w i
  measurable_toFun := swap_measurable w i
  measurable_invFun := swap_measurable w i

/-- Interchanging a genuine old gap and the fresh slack has absolute
Jacobian one, proved by a conditional one-dimensional reflection. -/
theorem swap_measurePreserving (w : ℝ) (i : Fin k) :
    MeasurePreserving (swap w i) volume volume := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1)=>ℝ) i
    have he : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n+1)=>ℝ) i
    have hs : MeasurePreserving
        (fun p : (Fin n→ℝ)×ℝ => (p.1,w-(∑ j,p.1 j)-p.2))
        (volume.prod volume) (volume.prod volume) := by
      apply (MeasurePreserving.id (volume : Measure (Fin n→ℝ))).skew_product
        (g:=fun t : Fin n→ℝ=>fun u : ℝ=>w-(∑ j,t j)-u)
      · exact (measurable_const.sub (Finset.measurable_sum _
          (fun j _=>(measurable_pi_apply j).comp measurable_fst))).sub measurable_snd
      · exact ae_of_all _ (fun t=>((volume : Measure ℝ).measurePreserving_sub_left (w-∑ j,t j)).map_eq)
    have hh := he.symm.comp (Measure.measurePreserving_swap.comp
      (hs.comp (Measure.measurePreserving_swap.comp he)))
    convert! hh using 1
    funext d
    have hsum := i.sum_univ_succAbove d
    ext j
    refine Fin.eq_self_or_eq_succAbove i j |>.elim ?_ ?_
    · intro hj
      subst j
      simp only [swap_same,slack]
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.removeNth_apply]
      rw [hsum]
      ring
    · rintro ⟨j,rfl⟩
      rw [swap_other w i (i.succAbove j) (Fin.succAbove_ne i j)]
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.removeNth_apply]

theorem integral_swap (w : ℝ) (i : Fin k) (F : (Fin k→ℝ)→ℝ) :
    (∫ d,F (swap w i d))=∫ d,F d :=
  (swap_measurePreserving w i).integral_comp (swapEquiv w i).measurableEmbedding F

theorem simplex_swap (w : ℝ) (i : Fin k) (d : Fin k→ℝ) :
    ((∀ j,0<swap w i d j) ∧ 0<slack w (swap w i d)) ↔
      ((∀ j,0<d j) ∧ 0<slack w d) := by
  constructor
  · rintro ⟨hd,hs⟩
    refine ⟨?_,?_⟩
    · intro j
      by_cases hj : j=i
      · subst j
        simpa only [slack_swap] using hs
      · simpa only [swap_other w i j hj] using hd j
    · simpa only [swap_same] using hd i
  · rintro ⟨hd,hs⟩
    refine ⟨?_,?_⟩
    · intro j
      by_cases hj : j=i
      · subst j
        simpa only [swap_same] using hs
      · simpa only [swap_other w i j hj] using hd j
    · simpa only [slack_swap] using hd i

end SHE.GapSimplexReflection
