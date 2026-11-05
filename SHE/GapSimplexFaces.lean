module

public import SHE.GapSimplexReflection
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.GapSimplexFaces
open Set MeasureTheory GapSimplexReflection
open scoped BigOperators
open Classical
variable {k : ℕ}

def simplex (w : ℝ) (d : Fin k→ℝ) : Prop := (∀ j,0<d j) ∧ 0<slack w d

theorem simplex_measurableSet (w : ℝ) : MeasurableSet {d : Fin k→ℝ | simplex w d} := by
  have hh := (OrderedGapCoordinates.simplex_measurableSet k w)
  convert! hh using 1
  ext d
  simp only [simplex,slack,mem_setOf_eq,sub_pos]

theorem coord_mem (w : ℝ) (d : Fin k→ℝ) (hd : simplex w d) (j : Fin k) : d j∈Ioo 0 w := by
  refine ⟨hd.1 j,?_⟩
  have hj : d j≤∑ l,d l := Finset.single_le_sum
    (fun l _=>(hd.1 l).le) (Finset.mem_univ j)
  have hs : (∑ l,d l)<w := by simpa only [slack,sub_pos] using hd.2
  exact hj.trans_lt hs

theorem slack_mem {w : ℝ} (hw : 0<w) (d : Fin k→ℝ) (hd : simplex w d) : slack w d∈Ioc 0 w := by
  refine ⟨hd.2,?_⟩
  have hs : 0≤∑ j,d j := Finset.sum_nonneg (fun j _=>(hd.1 j).le)
  dsimp only [slack]
  linarith

/-- One of the genuine gaps, including the fresh slack, carries a
fixed fraction of the full time window. -/
theorem exists_large_gap (w : ℝ) (d : Fin k→ℝ) :
    ∃ i : Fin (k+1),w/((k+1:ℕ):ℝ)≤(Fin.cons (slack w d) d : Fin (k+1)→ℝ) i := by
  by_contra h
  have hall : ∀ i : Fin (k+1),(Fin.cons (slack w d) d : Fin (k+1)→ℝ) i<w/((k+1:ℕ):ℝ) := by
    simpa only [not_exists,not_le] using h
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty : (Finset.univ : Finset (Fin (k+1))).Nonempty)
    (fun i _=>hall i)
  have hsum : (∑ i : Fin (k+1),(Fin.cons (slack w d) d : Fin (k+1)→ℝ) i)=w := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,slack]
    ring
  rw [hsum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hn : (0:ℝ)<((k+1:ℕ):ℝ) := by positivity
  have he : ((k+1:ℕ):ℝ)*(w/((k+1:ℕ):ℝ))=w := by field_simp
  rw [he] at hs
  exact lt_irrefl w hs

def cut (w : ℝ) (f : ℝ→ℝ) (t : ℝ) : ℝ := if t∈Ioo 0 w then f t else 0

def box (w : ℝ) (F : Fin k→ℝ→ℝ) (d : Fin k→ℝ) : ℝ := ∏ j,cut w (F j) (d j)

theorem cut_nonneg (w : ℝ) (f : ℝ→ℝ) (hf : ∀ t,0<t→0≤f t) (t : ℝ) : 0≤cut w f t := by
  unfold cut
  split_ifs with h
  · exact hf t h.1
  · exact le_rfl

theorem box_nonneg (w : ℝ) (F : Fin k→ℝ→ℝ) (hF : ∀ j t,0<t→0≤F j t) (d : Fin k→ℝ) :
    0≤box w F d := Finset.prod_nonneg (fun j _=>cut_nonneg w _ (hF j) _)

theorem box_eq (w : ℝ) (F : Fin k→ℝ→ℝ) (d : Fin k→ℝ) (hd : simplex w d) :
    box w F d=∏ j,F j (d j) := by
  apply Finset.prod_congr rfl
  intro j _
  exact if_pos (coord_mem w d hd j)

theorem box_integrable (w : ℝ) (F : Fin k→ℝ→ℝ) (hi : ∀ j,Integrable (cut w (F j))) :
    Integrable (box w F) := Integrable.fintype_prod hi

theorem box_integral (w : ℝ) (F : Fin k→ℝ→ℝ) :
    (∫ d,box w F d)=∏ j,∫ t,cut w (F j) t := integral_fintype_prod_volume_eq_prod _

def face (w : ℝ) (F : Fin (k+1)→ℝ→ℝ) : Fin (k+1)→(Fin k→ℝ)→ℝ :=
  Fin.cases (box w (fun j=>F j.succ))
    (fun i d=>box w (Function.update (fun j=>F j.succ) i (F 0)) (swap w i d))

theorem face_nonneg (w : ℝ) (F : Fin (k+1)→ℝ→ℝ)
    (hF : ∀ j t,0<t→0≤F j t) (i : Fin (k+1)) (d : Fin k→ℝ) : 0≤face w F i d := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact box_nonneg w _ (fun j=>hF j.succ) d
  · apply box_nonneg
    intro l t ht
    by_cases hl : l=j
    · subst l
      simpa using hF 0 t ht
    · simpa [Function.update_of_ne hl] using hF l.succ t ht

theorem face_integrable (w : ℝ) (F : Fin (k+1)→ℝ→ℝ)
    (hi : ∀ j,Integrable (cut w (F j))) (i : Fin (k+1)) : Integrable (face w F i) := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact box_integrable w _ (fun j=>hi j.succ)
  · change Integrable ((box w (Function.update (fun l=>F l.succ) j (F 0))) ∘ swap w j)
    apply (swap_measurePreserving w j).integrable_comp_of_integrable
    apply box_integrable
    intro l
    by_cases hl : l=j
    · subst l
      simpa using hi 0
    · simpa [Function.update_of_ne hl] using hi l.succ

theorem face_integral (w : ℝ) (F : Fin (k+1)→ℝ→ℝ) (i : Fin (k+1)) :
    (∫ d,face w F i d)=
      Fin.cases (∏ j : Fin k,∫ t,cut w (F j.succ) t)
        (fun l=>∏ j : Fin k,∫ t,cut w (Function.update (fun j=>F j.succ) l (F 0) j) t) i := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact box_integral w _
  · rw [face,Fin.cases_succ,integral_swap,box_integral,Fin.cases_succ]

def density (w : ℝ) (F : Fin (k+1)→ℝ→ℝ) (d : Fin k→ℝ) : ℝ :=
  if simplex w d then F 0 (slack w d)*(∏ j,F j.succ (d j)) else 0

theorem density_nonneg (w : ℝ) (F : Fin (k+1)→ℝ→ℝ)
    (hF : ∀ j t,0<t→0≤F j t) (d : Fin k→ℝ) : 0≤density w F d := by
  unfold density
  split_ifs with h
  · exact mul_nonneg (hF 0 _ h.2) (Finset.prod_nonneg (fun j _=>hF j.succ _ (h.1 j)))
  · exact le_rfl

theorem density_le_face {w : ℝ} (hw : 0<w) (F : Fin (k+1)→ℝ→ℝ)
    (hF : ∀ j t,0<t→0≤F j t) (A : Fin (k+1)→ℝ) (hA : ∀ i,0≤A i)
    (hcap : ∀ i t,w/((k+1:ℕ):ℝ)≤t→t≤w→F i t≤A i) (d : Fin k→ℝ) :
    density w F d≤∑ i,A i*face w F i d := by
  by_cases hd : simplex w d
  · obtain ⟨i,hi⟩ := exists_large_gap w d
    have hone : density w F d≤A i*face w F i d := by
      refine Fin.cases ?_ (fun j=>?_) i hi
      · intro hi
        simp only [Fin.cons_zero] at hi
        rw [density,if_pos hd,face,Fin.cases_zero,box_eq w _ d hd]
        exact mul_le_mul_of_nonneg_right (hcap 0 _ hi (slack_mem hw d hd).2)
          (Finset.prod_nonneg (fun j _=>hF j.succ _ (hd.1 j)))
      · intro hi
        simp only [Fin.cons_succ] at hi
        have hds : simplex w (swap w j d) := (simplex_swap w j d).mpr hd
        have hp : box w (Function.update (fun l=>F l.succ) j (F 0)) (swap w j d)=
            F 0 (slack w d)*(∏ l∈Finset.univ.erase j,F l.succ (d l)) := by
          rw [box_eq w _ _ hds,←Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
          simp only [Function.update_self,swap_same]
          congr 1
          apply Finset.prod_congr rfl
          intro l hl
          have hlj : l≠j := (Finset.mem_erase.mp hl).1
          rw [Function.update_of_ne hlj,swap_other w j l hlj]
        rw [density,if_pos hd,face,Fin.cases_succ,hp,
          ←Finset.mul_prod_erase Finset.univ (fun l=>F l.succ (d l)) (Finset.mem_univ j)]
        have hmul := mul_le_mul_of_nonneg_left (hcap j.succ _ hi (coord_mem w d hd j).2.le)
          (mul_nonneg (hF 0 _ hd.2) (Finset.prod_nonneg (s:=Finset.univ.erase j)
            (fun l _=>hF l.succ _ (hd.1 l))))
        convert! hmul using 1 <;> ring
    exact hone.trans (Finset.single_le_sum (fun j _=>mul_nonneg (hA j) (face_nonneg w F hF j d)) (Finset.mem_univ i))
  · rw [density,if_neg hd]
    exact Finset.sum_nonneg (fun i _=>mul_nonneg (hA i) (face_nonneg w F hF i d))

/-- Genuine simplex integration is bounded by the sum over its largest
gap faces. The reflected box integrals are actual product Lebesgue
integrals, so this does not assert independence of ordered gaps. -/
theorem density_integral_bound {w : ℝ} (hw : 0<w) (F : Fin (k+1)→ℝ→ℝ)
    (hm : ∀ i,Measurable (F i)) (hF : ∀ i t,0<t→0≤F i t)
    (hi : ∀ i,Integrable (cut w (F i))) (A : Fin (k+1)→ℝ) (hA : ∀ i,0≤A i)
    (hcap : ∀ i t,w/((k+1:ℕ):ℝ)≤t→t≤w→F i t≤A i) :
    Integrable (density w F) ∧
      (∫ d,density w F d)≤∑ i,A i*(∫ d,face w F i d) := by
  have hdom : Integrable (fun d=>∑ i,A i*face w F i d) :=
    integrable_finset_sum _ (fun i _=>(face_integrable w F hi i).const_mul _)
  have hmeas : Measurable (density w F) := by
    apply Measurable.ite (simplex_measurableSet w)
    · exact ((hm 0).comp (slack_measurable w)).mul
        (Finset.measurable_prod _ (fun j _=>(hm j.succ).comp (measurable_pi_apply j)))
    · exact measurable_const
  have hin : Integrable (density w F) := hdom.mono' hmeas.aestronglyMeasurable
    (ae_of_all _ (fun d=>by rw [Real.norm_of_nonneg (density_nonneg w F hF d)]; exact density_le_face hw F hF A hA hcap d))
  refine ⟨hin,?_⟩
  calc
    _ ≤ ∫ d,∑ i,A i*face w F i d := integral_mono hin hdom (density_le_face hw F hF A hA hcap)
    _ = _ := by rw [integral_finset_sum _ (fun i _=>(face_integrable w F hi i).const_mul _)]; simp only [integral_const_mul]

end SHE.GapSimplexFaces
