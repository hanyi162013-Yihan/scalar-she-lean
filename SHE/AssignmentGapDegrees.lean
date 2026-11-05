module

public import SHE.AllocatedAssignmentKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.AllocatedAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition RootPowerGapKernels
open scoped BigOperators
open Classical
variable {k m : ℕ}

def roughCount (cs : List (Fin k×Fin (m+1))) : ℕ :=
  (Finset.univ.filter (fun l : Fin (m+1)=>l≠0 ∧ block cs l≠[])).card

def rootCount (cs : List (Fin k×Fin (m+1))) : ℕ := (block cs 0).length

def inverseDegreeProduct (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) (a : ℝ) : ℝ :=
  ∏ i,if rootFlag cs hc i then 1 else 1/degree cs hc a i

theorem root_count_eq (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) :
    (Finset.univ.filter (fun i=>rootFlag cs hc i=true)).card=rootCount cs := by
  have he : (Finset.univ.filter (fun i=>rootFlag cs hc i=true))=
      Finset.univ.filter (fun i=>label cs hc i=0) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,rootFlag,decide_eq_true_eq]
  rw [he]
  exact block_length cs hc 0

theorem total_degree (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) (a : ℝ) :
    (∑ i,if rootFlag cs hc i then 0 else degree cs hc a i)=a*(roughCount cs:ℝ) := by
  have he : (∑ i,if rootFlag cs hc i then 0 else degree cs hc a i)=
      ∑ i,if label cs hc i=0 then 0 else a/((block cs (label cs hc i)).length:ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : label cs hc i=0 <;> simp only [rootFlag,degree,hi,decide_true,decide_false,
      Bool.false_eq_true,ite_true,ite_false]
  rw [he,←dependent_sum_blocks cs hc (fun l _=>if l=0 then 0 else a/((block cs l).length:ℝ))]
  have hb (l : Fin (m+1)) : (∑ _j : Fin (block cs l).length,if l=0 then 0 else a/((block cs l).length:ℝ))=
      if l≠0 ∧ block cs l≠[] then a else 0 := by
    by_cases hl : l=0
    · simp only [hl,ite_true,ne_eq,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero]
    · by_cases hn : block cs l=[]
      · have hempty : IsEmpty (Fin (block cs l).length) := by
          rw [hn,List.length_nil]
          infer_instance
        letI := hempty
        simp [hn]
      · simp only [hl,ite_false,ne_eq,not_false_eq_true,hn,true_and,ite_true,
          Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hlen : (0:ℝ) < (block cs l).length := by
          exact_mod_cast List.length_pos_iff_ne_nil.mpr hn
        field_simp [ne_of_gt hlen]
  simp_rw [hb]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,roughCount]
  ring

theorem inverseDegreeProduct_nonneg (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    0 ≤ inverseDegreeProduct cs hc a := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact zero_le_one
  · exact div_nonneg zero_le_one (degree_pos_le_one cs hc ha ha1 i).1.le

end SHE.AllocatedAssignmentKernel

namespace SHE.RootPowerGapKernels
open Set MeasureTheory Real
open scoped BigOperators
open Classical
variable {ι : Type*} [DecidableEq ι]

/-- Exact factorization of the finite mass product into root masses,
total positive degree, and reciprocal-degree constants. -/
theorem prod_mass {ν w : ℝ} (hw : 0<w) (p : ι→ℝ) (root : ι→Bool) (s : Finset ι) :
    (∏ i∈s,mass ν (p i) (root i) w)=
      (∏ i∈s,if root i then 1 else 1/p i)*
        w^(∑ i∈s,if root i then 0 else p i)*
        rootMass ν w^((s.filter (fun i=>root i=true)).card) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    simp only [Finset.prod_insert his,Finset.sum_insert his]
    rw [ih]
    cases hi : root i
    · simp only [hi,Bool.false_eq_true,ite_false,mass]
      have he : (insert i s).filter (fun j=>root j=true)=s.filter (fun j=>root j=true) := by
        rw [Finset.filter_insert]
        simp only [hi,Bool.false_eq_true,ite_false]
      rw [he,Real.rpow_add hw]
      ring
    · simp only [hi,ite_true,mass]
      have he : ((insert i s).filter (fun j=>root j=true)).card=
          (s.filter (fun j=>root j=true)).card+1 := by
        rw [Finset.filter_insert,if_pos hi,Finset.card_insert_of_notMem]
        exact fun h=>his (Finset.mem_filter.mp h).1
      rw [he,pow_succ]
      simp only [zero_add,one_mul]
      ring

end SHE.RootPowerGapKernels
