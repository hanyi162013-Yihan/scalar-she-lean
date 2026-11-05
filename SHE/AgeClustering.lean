module

public import SHE.Algebra
public import Mathlib.Data.List.Sort

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.AgeClustering
open List
variable {ι : Type*}

/-- Actual minimum and maximum members of a nonempty age block. -/
def BlockBound (s : ι → ℝ) (A : ℝ) (n : ℕ) (B : List ι) : Prop :=
  ∃ lo ∈ B, ∃ hi ∈ B, 0 < s lo ∧
    (∀ i ∈ B,s lo ≤ s i ∧ s i ≤ s hi) ∧ s hi ≤ A^n*s lo

def Separated (s : ι → ℝ) (A : ℝ) (B C : List ι) : Prop :=
  ∀ i ∈ B,∀ j ∈ C,A*s i ≤ s j

theorem bound_nonempty {s : ι → ℝ} {A : ℝ} {n : ℕ} {B : List ι}
    (hB : BlockBound s A n B) : B ≠ [] := by
  obtain ⟨lo,hlo,_⟩ := hB
  intro he
  simpa only [he,List.not_mem_nil] using hlo

theorem bound_mono {s : ι → ℝ} {A : ℝ} (hA : 1 ≤ A) {n m : ℕ} (hnm : n ≤ m)
    {B : List ι} (hB : BlockBound s A n B) : BlockBound s A m B := by
  obtain ⟨lo,hlo,hi,hhi,hpos,hbounds,hbound⟩ := hB
  exact ⟨lo,hlo,hi,hhi,hpos,hbounds,hbound.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hnm) hpos.le)⟩

theorem singleton_bound {s : ι → ℝ} {A : ℝ} (hA : 1 ≤ A) (n : ℕ) (x : ι)
    (hx : 0 < s x) : BlockBound s A n [x] := by
  have hp : 1 ≤ A^n := one_le_pow₀ hA
  refine ⟨x,by simp,x,by simp,hx,?_,?_⟩
  · intro i hi
    have he : i=x := by simpa only [List.mem_singleton] using hi
    simp only [he,le_refl,and_self]
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hx.le

/-- Ordered positive ages split into nonempty separated blocks. Adding
a new minimum either starts a block or enlarges the first block by at
most one factor A. -/
theorem sorted_blocks (s : ι → ℝ) {A : ℝ} (hA : 1 ≤ A) (l : List ι)
    (hpos : ∀ i ∈ l,0 < s i) (hsort : l.Pairwise (fun i j => s i ≤ s j)) :
    ∃ blocks : List (List ι),blocks.flatten=l ∧
      (∀ B ∈ blocks,BlockBound s A l.length B) ∧ blocks.Pairwise (Separated s A) := by
  induction l with
  | nil => exact ⟨[],rfl,by simp,by simp⟩
  | cons x l ih =>
    have hx : 0 < s x := hpos x (by simp)
    have hxall := (List.pairwise_cons.mp hsort).1
    have htail := (List.pairwise_cons.mp hsort).2
    obtain ⟨blocks,hflat,hbounds,hsep⟩ := ih
      (fun i hi => hpos i (List.mem_cons_of_mem x hi)) htail
    have hwiden : ∀ B ∈ blocks,BlockBound s A (x::l).length B :=
      fun B hB => bound_mono hA (by simp) (hbounds B hB)
    cases blocks with
    | nil =>
      have hl : l=[] := by simpa only [List.flatten_nil] using hflat.symm
      subst l
      refine ⟨[[x]],rfl,?_,by simp⟩
      intro B hB
      have he : B=[x] := List.mem_singleton.mp hB
      subst B
      exact singleton_bound hA 1 x hx
    | cons B rest =>
      obtain ⟨lo,hlo,hi,hhi,hloPos,hwithin,hratio⟩ := hbounds B (by simp)
      have hloL : lo ∈ l := by rw [← hflat]; exact List.mem_flatten.mpr ⟨B,by simp,hlo⟩
      have hhiL : hi ∈ l := by rw [← hflat]; exact List.mem_flatten.mpr ⟨B,by simp,hhi⟩
      have hBrest := (List.pairwise_cons.mp hsep).1
      have hrest := (List.pairwise_cons.mp hsep).2
      by_cases hgap : A*s x ≤ s lo
      · refine ⟨[x]::B::rest,?_,?_,?_⟩
        · simpa only [List.flatten_cons,List.singleton_append] using congrArg (List.cons x) hflat
        · intro C hC
          rcases List.mem_cons.mp hC with rfl | hC
          · exact singleton_bound hA _ x hx
          · exact hwiden C hC
        · apply List.pairwise_cons.mpr
          refine ⟨?_,hsep⟩
          intro C hC i hi' j hj
          have hix : i=x := by simpa only [List.mem_singleton] using hi'
          subst i
          rcases List.mem_cons.mp hC with rfl | hC
          · exact hgap.trans (hwithin j hj).1
          · exact (mul_le_mul_of_nonneg_left (hxall lo hloL) (by linarith)).trans
              (hBrest C hC lo hlo j hj)
      · refine ⟨(x::B)::rest,?_,?_,?_⟩
        · simpa only [List.flatten_cons,List.cons_append] using congrArg (List.cons x) hflat
        · intro C hC
          rcases List.mem_cons.mp hC with rfl | hC
          · refine ⟨x,by simp,hi,List.mem_cons_of_mem x hhi,hx,?_,?_⟩
            · intro i hi'
              rcases List.mem_cons.mp hi' with rfl | hi'
              · exact ⟨le_rfl,hxall hi hhiL⟩
              · have hiL : i ∈ l := by rw [← hflat]; exact List.mem_flatten.mpr ⟨B,by simp,hi'⟩
                exact ⟨hxall i hiL,(hwithin i hi').2⟩
            · have hclose : s lo ≤ A*s x := le_of_not_ge hgap
              have hm := mul_le_mul_of_nonneg_left hclose (pow_nonneg (by linarith : 0 ≤ A) l.length)
              have he : A^l.length*(A*s x)=A^((x::l).length)*s x := by simp only [List.length_cons,pow_succ]; ring
              exact hratio.trans (hm.trans_eq he)
          · exact hwiden C (List.mem_cons_of_mem B hC)
        · apply List.pairwise_cons.mpr
          refine ⟨?_,hrest⟩
          intro C hC i hi' j hj
          rcases List.mem_cons.mp hi' with rfl | hi'
          · exact (mul_le_mul_of_nonneg_left (hxall lo hloL) (by linarith)).trans
              (hBrest C hC lo hlo j hj)
          · exact hBrest C hC i hi' j hj

theorem nonempty_block_count (blocks : List (List ι))
    (hb : ∀ B ∈ blocks,B ≠ []) : blocks.length ≤ blocks.flatten.length := by
  induction blocks with
  | nil => simp
  | cons B rest ih =>
    have hrest := ih (fun C hC => hb C (List.mem_cons_of_mem B hC))
    have hB := hb B (by simp)
    have hlen : 1 ≤ B.length := by
      cases B with
      | nil => exact (hB rfl).elim
      | cons a l => simp
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    omega

/-- The block decomposition for an arbitrary list preserves every
index, including its multiplicity, up to a permutation. -/
theorem blocks (s : ι → ℝ) {A : ℝ} (hA : 1 ≤ A) (l : List ι)
    (hpos : ∀ i ∈ l,0 < s i) :
    ∃ bs : List (List ι),bs.flatten.Perm l ∧ bs.length ≤ l.length ∧
      (∀ B ∈ bs,BlockBound s A l.length B) ∧ bs.Pairwise (Separated s A) := by
  classical
  let cmp : ι → ι → Bool := fun i j => decide (s i ≤ s j)
  let sorted := l.mergeSort cmp
  have hp : sorted.Perm l := List.mergeSort_perm l cmp
  have hs : sorted.Pairwise (fun i j => s i ≤ s j) := by
    have ht (a b c : ι) (hab : cmp a b=true) (hbc : cmp b c=true) : cmp a c=true := by
      simpa only [cmp,decide_eq_true_eq] using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)
    have htotal (a b : ι) : (cmp a b || cmp b a)=true := by
      simpa only [cmp,Bool.or_eq_true,decide_eq_true_eq] using le_total (s a) (s b)
    simpa only [sorted,cmp,decide_eq_true_eq] using List.pairwise_mergeSort ht htotal l
  obtain ⟨bs,hflat,hbound,hsep⟩ := sorted_blocks s hA sorted
    (fun i hi => hpos i (hp.mem_iff.mp hi)) hs
  have hperm : bs.flatten.Perm l := hflat ▸ hp
  refine ⟨bs,hperm,?_,?_,hsep⟩
  · exact (nonempty_block_count bs (fun B hB => bound_nonempty (hbound B hB))).trans_eq hperm.length_eq
  · simpa only [hp.length_eq] using hbound

end SHE.AgeClustering
