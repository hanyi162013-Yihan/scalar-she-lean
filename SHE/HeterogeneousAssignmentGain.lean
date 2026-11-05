module

public import SHE.AssignmentGapGain
public import SHE.HeterogeneousSimplexIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section
namespace SHE.HeterogeneousAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition
open scoped BigOperators
open Classical
variable {k:ℕ}

def gainBlock (cs:List (Fin k×Fin (k+1))) (ν:ℝ) (a:Fin (k+1)→ℝ) (d:Fin k→ℝ) (l:Fin (k+1)):ℝ:=
  if l=0 then ∏j:Fin (block cs l).length,min 1 (ν*(d ((block cs l).get j))^(1/4:ℝ))
  else if h:block cs l=[] then 1 else (d (MinimumGapChoice.choose d (block cs l) h))^(a l)

def gain (cs:List (Fin k×Fin (k+1))) (ν:ℝ) (a:Fin (k+1)→ℝ) (d:Fin k→ℝ):ℝ:=
  ∏l,gainBlock cs ν a d l

def emptyGain (cs:List (Fin k×Fin (k+1))) (a:Fin (k+1)→ℝ) (age:Fin k→ℝ):ℝ:=
  ∏j,if block cs j.succ=[] then (age j)^(a j.succ) else 1

theorem inverse_mul_gain_eq_weight (cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k)) (ν:ℝ) (a:Fin (k+1)→ℝ) (d:Fin k→ℝ):
    (∏i,(d i)⁻¹)*gain cs ν a d=weight cs ν a d := by
  have hb(l:Fin (k+1)):blockWeight cs ν a d l=
      (∏j:Fin (block cs l).length,(d ((block cs l).get j))⁻¹)*gainBlock cs ν a d l := by
    unfold blockWeight gainBlock
    split_ifs with hl hempty
    · rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      simp only [SHE.rootKernel,Real.rpow_neg_one]
    · have hi:IsEmpty (Fin (block cs l).length):=by rw [hempty,List.length_nil];infer_instance
      letI:=hi
      simp
    · rfl
  rw [←prod_blocks cs hc (fun i=>(d i)⁻¹)]
  unfold gain weight
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  exact (hb l).symm

theorem gain_eq_root_rough (cs:List (Fin k×Fin (k+1))) (ν:ℝ) (a:Fin (k+1)→ℝ) (d:Fin k→ℝ):
    gain cs ν a d=
      (∏j:Fin (block cs 0).length,min 1 (ν*(d ((block cs 0).get j))^(1/4:ℝ)))*
      ∏j:Fin k,if h:block cs j.succ=[] then 1 else
        (d (MinimumGapChoice.choose d (block cs j.succ) h))^(a j.succ) := by
  rw [gain,Fin.prod_univ_succ]
  simp only [gainBlock,ite_true,Fin.succ_ne_zero,ite_false]

/-- Every original empty leaf keeps its OWN degree, including the
paired leaf's complementary degree; no age is dropped from the ledger. -/
theorem emptyGain_bound (cs:List (Fin k×Fin (k+1))) (a:Fin (k+1)→ℝ)
    (ha:∀j:Fin k,0≤a j.succ) {w:ℝ} (hw:0<w) (age:Fin k→ℝ)
    (hage:∀j,0≤age j ∧ age j≤w):
    emptyGain cs a age≤w^(emptyDegree cs a) := by
  have hh:emptyGain cs a age≤∏j:Fin k,if block cs j.succ=[] then w^(a j.succ) else 1 := by
    unfold emptyGain
    apply Finset.prod_le_prod₀
    · intro j _
      split_ifs <;> first |exact Real.rpow_nonneg (hage j).1 _|exact zero_le_one
    · intro j _
      split_ifs
      · exact Real.rpow_le_rpow (hage j).1 (hage j).2 (ha j)
      · exact le_rfl
  refine hh.trans_eq ?_
  have he:emptyDegree cs a=∑j:Fin k,if block cs j.succ=[] then a j.succ else 0 := by
    unfold emptyDegree
    rw [Fin.sum_univ_succ]
    simp only [ne_eq,not_true_eq_false,false_and,ite_false,Fin.succ_ne_zero,not_false_eq_true,true_and,zero_add]
  rw [he,Real.rpow_sum_of_pos hw]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hb:block cs j.succ=[] <;> simp only [hb,ite_true,ite_false,Real.rpow_zero]

end SHE.HeterogeneousAssignmentKernel
