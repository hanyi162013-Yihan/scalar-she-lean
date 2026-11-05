module
public import SHE.AgePartition
public import SHE.DefectCombinedTime
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.AgeBlockPairSum
open Finset

 theorem rep_injective {n:ℕ}{s:Fin n→ℝ}{A:ℝ}(P:AgeClustering.Partition s A):
    Function.Injective P.rep:=by
  intro i j hij
  simpa only [P.label_rep] using congrArg P.label hij

 theorem sum_le {m n:ℕ}(f:Fin m→Fin n) (hf:Function.Injective f)
    (g:Fin n→ℝ) (hg:∀ i,0≤g i): (∑ i,g (f i))≤∑ i,g i:=by
  classical
  rw [←Finset.sum_image (fun i _ j _ hij=>hf hij)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>hg i)

/-- Representative pairs form an actual subset of the original pairs. -/
 theorem pairs {n:ℕ}{s:Fin n→ℝ}{A:ℝ}(P:AgeClustering.Partition s A)
    (K:Fin n→Fin n→ℝ) (hK:∀ i j,0≤K i j):
    (∑ i:Fin P.count,∑ j:Fin P.count,K (P.rep i) (P.rep j))≤∑ i:Fin n,∑ j:Fin n,K i j:=by
  calc
    _≤∑ i:Fin P.count,∑ j:Fin n,K (P.rep i) j:=
      Finset.sum_le_sum (fun i _=>sum_le P.rep (rep_injective P) _ (hK (P.rep i)))
    _≤_:=sum_le P.rep (rep_injective P) _ (fun i=>Finset.sum_nonneg (fun j _=>hK i j))

 theorem kernel {n:ℕ}{target:Fin n→ℝ}{terminal A Λ ρ q:ℝ}
    (P:AgeClustering.Partition (fun i=>target i-terminal) A)
    (hΛ:0≤Λ) (hages:∀ i,terminal≤target i) (hq:q≤terminal):
    (∑ i:Fin P.count,∑ j:Fin P.count,
      DefectCombinedTime.kernel Λ ρ (P.lower i) (P.lower j) (terminal-q))≤
    ∑ i:Fin n,∑ j:Fin n,
      DefectCombinedTime.kernel Λ ρ (target i-terminal) (target j-terminal) (terminal-q):=by
  simp_rw [P.lower_eq_rep]
  exact pairs P _ (fun i j=>DefectCombinedTime.nonneg hΛ
    (sub_nonneg.mpr (hages i)) (sub_nonneg.mpr (hages j)) (sub_nonneg.mpr hq))
end SHE.AgeBlockPairSum
