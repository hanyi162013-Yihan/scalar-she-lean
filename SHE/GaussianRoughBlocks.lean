module

public import SHE.GaussianAssignmentSupport
public import SHE.GaussianRoughMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

/-! Actual vector old-fraction rough blocks. A nonempty assigned block
uses any one of its original Gaussian increments, with a finite-order
factor; foreign suppression never substitutes another increment law. -/
namespace SHE.GaussianRoughBlocks
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement
  GaussianVectorFractions GaussianAssignmentBlocks
open scoped InnerProductSpace BigOperators
variable {E:Type*}[Zero E]{n m:ℕ}

theorem difference_comm (i j:Fin n)(F:(Fin n→E)→ℝ):
    fractionDifference i (fractionDifference j F)=fractionDifference j (fractionDifference i F):=by
  classical
  funext x
  dsimp[fractionDifference]
  by_cases h:i=j
  · subst j;rfl
  · rw[Function.update_comm h];ring

theorem difference_comm_differences (i:Fin n)(is:List (Fin n))(F:(Fin n→E)→ℝ):
    fractionDifference i (fractionDifferences is F)=fractionDifferences is (fractionDifference i F):=by
  induction is with
  | nil=>rfl
  | cons j is ih=>
    change fractionDifference i (fractionDifference j (fractionDifferences is F))=_
    rw[difference_comm,ih]
    rfl

theorem coordinate_bound (i:Fin n)(is:List (Fin n))(hi:i∉is)(F:(Fin n→E)→ℝ)
    (B:E→ℝ)(hB:∀x,|F x|≤B (x i))(x:Fin n→E):
    |fractionDifferences is F x|≤2^is.length*B (x i):=by
  induction is generalizing x with
  | nil=>simpa[fractionDifferences] using hB x
  | cons j is ih=>
    have hij:i≠j:=fun h=>hi (by simp[h])
    have hit:i∉is:=fun h=>hi (List.mem_cons_of_mem _ h)
    have h1:=ih hit x
    have h2:=ih hit (Function.update x j 0)
    rw[Function.update_of_ne hij] at h2
    change |fractionDifferences is F x-fractionDifferences is F (Function.update x j 0)|≤_
    have hh:=abs_sub (fractionDifferences is F x) (fractionDifferences is F (Function.update x j 0))
    simp only[List.length_cons,pow_succ]
    nlinarith

theorem block_bound (is:List (Fin n))(hnd:is.Nodup)(F:(Fin n→E)→ℝ)(i:Fin n)(hi:i∈is)
    (B:E→ℝ)(hB:∀x,|fractionDifference i F x|≤B (x i))(x:Fin n→E):
    |fractionDifferences is F x|≤2^(is.length-1)*B (x i):=by
  induction is generalizing x with
  | nil=>simp at hi
  | cons j is ih=>
    obtain ⟨hj,hnd⟩:=List.nodup_cons.mp hnd
    by_cases hij:i=j
    · subst j
      change |fractionDifference i (fractionDifferences is F) x|≤_
      rw[difference_comm_differences]
      simpa using coordinate_bound i is hj (fractionDifference i F) B hB x
    · have hit:i∈is:=(List.mem_cons.mp hi).resolve_left hij
      have h1:=ih hnd hit x
      have h2:=ih hnd hit (Function.update x j 0)
      rw[Function.update_of_ne hij] at h2
      have hlen : 1 ≤ is.length:=List.length_pos_iff.mpr (List.ne_nil_of_mem hit)
      have hp:(2:ℝ)^is.length=2^(is.length-1)*2:=by rw[←pow_succ,Nat.sub_add_cancel hlen]
      change |fractionDifferences is F x-fractionDifferences is F (Function.update x j 0)|≤_
      have hh:=abs_sub (fractionDifferences is F x) (fractionDifferences is F (Function.update x j 0))
      simp only[List.length_cons,Nat.add_sub_cancel]
      rw[hp]
      nlinarith

section Linear
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]

def affineSum (m:ℝ)(L:Fin n→V→L[ℝ] ℝ)(x:Fin n→V):ℝ:=m+∑j,L j (x j)

theorem affineSum_update (m:ℝ)(L:Fin n→V→L[ℝ] ℝ)(x:Fin n→V)(i:Fin n):
    affineSum m L x-affineSum m L (Function.update x i 0)=L i (x i):=by
  classical
  dsimp[affineSum]
  rw[add_sub_add_left_eq_sub,←Finset.sum_sub_distrib]
  rw[Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp[Function.update_of_ne hji]
  · simp

theorem rough_difference_bound (a:ℝ→ℝ)(H β:ℝ)
    (hholder:∀z w,|a z-a w|≤H*|z-w|^β)(m:ℝ)(L:Fin n→V→L[ℝ] ℝ)(i:Fin n)(x:Fin n→V):
    |fractionDifference i (fun y=>a (affineSum m L y)) x|≤H*|L i (x i)|^β:=by
  simpa only[fractionDifference,affineSum_update] using
    hholder (affineSum m L x) (affineSum m L (Function.update x i 0))

theorem rough_block_bound (is:List (Fin n))(hnd:is.Nodup)(i:Fin n)(hi:i∈is)
    (a:ℝ→ℝ)(H β:ℝ)(hholder:∀z w,|a z-a w|≤H*|z-w|^β)
    (m:ℝ)(L:Fin n→V→L[ℝ] ℝ)(x:Fin n→V):
    |fractionDifferences is (fun y=>a (affineSum m L y)) x|≤
      (2:ℝ)^(is.length-1)*H*|L i (x i)|^β:=by
  convert! block_bound is hnd _ i hi (fun z=>H*|L i z|^β)
    (fun y=>rough_difference_bound a H β hholder m L i y) x using 1
  ring

theorem suppressed_rough_block_bound (choices:List (Fin n×Fin m))(hnd:(choices.map Prod.fst).Nodup)
    (k:Fin m)(i:Fin n)(hi:i∈block choices k)(a:ℝ→ℝ)(H β:ℝ)
    (hholder:∀z w,|a z-a w|≤H*|z-w|^β)(mean:ℝ)(L:Fin n→V→L[ℝ] ℝ)(x:Fin n→V):
    |fractionDifferences (block choices k) (fun y=>a (affineSum mean L y))
      (suppress (suppressed choices k) x)|≤
        (2:ℝ)^((block choices k).length-1)*H*|L i (x i)|^β:=by
  have hh:=rough_block_bound (block choices k) (block_nodup choices hnd k) i hi a H β hholder mean L
    (suppress (suppressed choices k) x)
  rwa[suppress_assigned_coordinate choices hnd k hi x] at hh

end Linear
end SHE.GaussianRoughBlocks
