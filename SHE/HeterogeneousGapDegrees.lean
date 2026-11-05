module

public import SHE.HeterogeneousAssignmentKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.HeterogeneousAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition
open scoped BigOperators
open Classical
variable {k : ℕ}

def assignedDegree (cs : List (Fin k×Fin (k+1))) (a : Fin (k+1)→ℝ) : ℝ :=
  ∑ l,if l≠0 ∧ block cs l≠[] then a l else 0

def emptyDegree (cs : List (Fin k×Fin (k+1))) (a : Fin (k+1)→ℝ) : ℝ :=
  ∑ l,if l≠0 ∧ block cs l=[] then a l else 0

def inverseDegreeProduct (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (a : Fin (k+1)→ℝ) : ℝ :=
  ∏ i,if rootFlag cs hc i then 1 else 1/degree cs hc a i

theorem root_count_eq (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) :
    (Finset.univ.filter (fun i=>rootFlag cs hc i=true)).card=AllocatedAssignmentKernel.rootCount cs := by
  exact AllocatedAssignmentKernel.root_count_eq cs hc

/-- Each rough block receives its OWN total degree, including the
single paired block with degree (beta-chi)/4. -/
theorem total_degree (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (a : Fin (k+1)→ℝ) :
    (∑ i,if rootFlag cs hc i then 0 else degree cs hc a i)=assignedDegree cs a := by
  have he : (∑ i,if rootFlag cs hc i then 0 else degree cs hc a i)=
      ∑ i,if label cs hc i=0 then 0 else a (label cs hc i)/((block cs (label cs hc i)).length:ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : label cs hc i=0 <;> simp only [rootFlag,degree,hi,decide_true,decide_false,
      Bool.false_eq_true,ite_true,ite_false]
  rw [he,←dependent_sum_blocks cs hc (fun l _=>if l=0 then 0 else a l/((block cs l).length:ℝ))]
  have hb (l : Fin (k+1)) : (∑ _j : Fin (block cs l).length,if l=0 then 0 else a l/((block cs l).length:ℝ))=
      if l≠0 ∧ block cs l≠[] then a l else 0 := by
    by_cases hl : l=0
    · simp only [hl,ite_true,ne_eq,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero]
    · by_cases hn : block cs l=[]
      · have hempty : IsEmpty (Fin (block cs l).length) := by
          rw [hn,List.length_nil]
          infer_instance
        haveI := hempty
        simp [hn]
      · simp only [hl,ite_false,ne_eq,not_false_eq_true,hn,true_and,ite_true,
          Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hlen : (0:ℝ) < (block cs l).length := by
          exact_mod_cast List.length_pos_iff_ne_nil.mpr hn
        field_simp [ne_of_gt hlen]
  simp_rw [hb]
  rfl

/-- Empty native leaves keep their full age powers. Together with
assigned degrees this counts EVERY rough factor exactly once. -/
theorem assigned_add_empty (cs : List (Fin k×Fin (k+1))) (a : Fin (k+1)→ℝ) :
    assignedDegree cs a+emptyDegree cs a=∑ j : Fin k,a j.succ := by
  unfold assignedDegree emptyDegree
  rw [←Finset.sum_add_distrib]
  have he : (∑ l : Fin (k+1),((if l≠0 ∧ block cs l≠[] then a l else 0)+
      (if l≠0 ∧ block cs l=[] then a l else 0)))=
      ∑ l : Fin (k+1),if l=0 then 0 else a l := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases h0 : l=0 <;> by_cases hb : block cs l=[] <;> simp [h0,hb]
  rw [he,Fin.sum_univ_succ]
  simp only [ite_true,Fin.succ_ne_zero,ite_false,zero_add]

def pairedDegree (β χ : ℝ) (j0 : Fin k) (l : Fin (k+1)) : ℝ :=
  if l=j0.succ then (β-χ)/4 else β/4

theorem pairedDegree_pos_le_one {β χ : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hχ : 0≤χ) (hχβ : χ<β) (j0 : Fin k) (l : Fin (k+1)) :
    0<pairedDegree β χ j0 l ∧ pairedDegree β χ j0 l≤1 := by
  unfold pairedDegree
  split_ifs <;> constructor <;> linarith

/-- Pairing one rough factor costs ONLY chi/4 in the full finite-depth
degree, regardless of the number or shape of other assigned blocks. -/
theorem paired_total_degree (cs : List (Fin k×Fin (k+1))) (β χ : ℝ) (j0 : Fin k) :
    assignedDegree cs (pairedDegree β χ j0)+emptyDegree cs (pairedDegree β χ j0)=
      (k:ℝ)*β/4-χ/4 := by
  rw [assigned_add_empty]
  have he (j : Fin k) : pairedDegree β χ j0 j.succ=β/4-(if j=j0 then χ/4 else 0) := by
    by_cases hj : j=j0 <;> simp [pairedDegree,hj,Fin.succ_inj] <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

end SHE.HeterogeneousAssignmentKernel
