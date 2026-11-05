module
public import SHE.PhysicalWordHolder

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory GaussianIncrement StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates PhysicalScoreChain
open scoped BigOperators
local instance physicalLeafHolder_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n N:ℕ} (L:Level R X n)

/-- Every genuine centered coefficient leaf has the original coefficient
Hölder modulus. Its moving physical baseline cancels exactly. -/
theorem leaves_directional_holder {H β:ℝ}
    (hh:∀s t,|R.totalVariance s-R.totalVariance t|≤H*|s-t|^β)
    (k:ℕ)(p:History X k)(g:Fin (n+k)→Fin N)(j:Fin k)(d x:WordRecursion.State N)(s t:ℝ):
    |leaves L k p g j (x+s • d)-leaves L k p g j (x+t • d)|≤
      (H/2*|d (leafIndex k g j)|^β)*|s-t|^β:=by
  let i:=leafIndex k g j
  have h:=hh ((x+s • d) i) ((x+t • d) i)
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at h
  rw [show x i+s*d i-(x i+t*d i)=(s-t)*d i by ring,abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _)] at h
  change |(1/2:ℝ)*(R.totalVariance ((x+s • d) i)-baseline L k p j)-
    (1/2:ℝ)*(R.totalVariance ((x+t • d) i)-baseline L k p j)|≤_
  rw [show (1/2:ℝ)*(R.totalVariance ((x+s • d) i)-baseline L k p j)-
      (1/2:ℝ)*(R.totalVariance ((x+t • d) i)-baseline L k p j)=
      (1/2:ℝ)*(R.totalVariance ((x+s • d) i)-R.totalVariance ((x+t • d) i)) by ring,
    abs_mul,abs_of_pos (by norm_num:(0:ℝ)<1/2)]
  simpa only [i,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv,
    mul_assoc,mul_comm,mul_left_comm,one_mul] using mul_le_mul_of_nonneg_left h (by norm_num:(0:ℝ)≤1/2)

/-- The actual all-leaf word has a derivative-free directional Hölder
bound. No coefficient-approximation derivative occurs in the constant. -/
theorem word_directional_holder {A B H K β:ℝ} (hA:0≤A)(hB:0≤B)(hH:0≤H)(hK:0≤K)
    (ha:∀z,|R.totalVariance z|≤A) (hroot:∀p z,|L.test p z|≤B)
    (hh:∀s t,|R.totalVariance s-R.totalVariance t|≤H*|s-t|^β)
    (k:ℕ)(p:History X k)(g:Fin (n+k)→Fin N)(d:WordRecursion.State N)
    (hr:∀x s t,|initial L k p g (x+s • d)-initial L k p g (x+t • d)|≤K*|s-t|^β)
    (x:WordRecursion.State N)(s t:ℝ):
    |word L k p g (x+s • d)-word L k p g (x+t • d)|≤
      (1+B+(A+R.upper)/2)^(k+1)*
        (K+H/2*(∑j:Fin k,|d (leafIndex k g j)|^β))*|s-t|^β:=by
  let C:=1+B+(A+R.upper)/2
  have hC:1≤C:=by dsimp [C];linarith [R.upper_nonneg]
  let F:Fin (k+1)→WordRecursion.State N→ℝ:=Fin.cons (initial L k p g) (leaves L k p g)
  let D:Fin (k+1)→ℝ:=Fin.cons K (fun j=>H/2*|d (leafIndex k g j)|^β)
  have hcap:∀i y,|F i y|≤C:=by
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · intro y
      exact (hroot _ _).trans (by dsimp [C];linarith [R.upper_nonneg])
    · intro y
      have hb:|leaves L k p g j y|≤(A+R.upper)/2:=by
        unfold leaves
        rw [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<1/2)]
        have h:|R.totalVariance (y (leafIndex k g j))-baseline L k p j|≤A+R.upper:=
          (abs_sub _ _).trans (add_le_add (ha _) (R.reference_bound _))
        nlinarith
      exact hb.trans (by dsimp [C];linarith)
  have hD:∀i,0≤D i:=by
    intro i
    refine Fin.cases hK (fun j=>?_) i
    exact mul_nonneg (div_nonneg hH (by norm_num)) (Real.rpow_nonneg (abs_nonneg _) _)
  have hdiff:∀i,|F i (x+s • d)-F i (x+t • d)|≤D i*|s-t|^β:=by
    intro i
    refine Fin.cases (hr x s t) (fun j=>?_) i
    exact leaves_directional_holder L hh k p g j d x s t
  have hp:=FiniteProductHolder.difference_bound Finset.univ
    (fun i=>F i (x+s • d)) (fun i=>F i (x+t • d)) (fun i=>D i*|s-t|^β) hC
    (fun i _=>hcap i _) (fun i _=>hcap i _)
    (fun i _=>mul_nonneg (hD i) (Real.rpow_nonneg (abs_nonneg _) _)) (fun i _=>hdiff i)
  simp only [Finset.card_univ,Fintype.card_fin,Fin.prod_univ_succ,Fin.sum_univ_succ,
    F,D,Fin.cons_zero,Fin.cons_succ] at hp
  have hsum:(∑j:Fin k,(H/2*|d (leafIndex k g j)|^β)*|s-t|^β)=
      (H/2*(∑j:Fin k,|d (leafIndex k g j)|^β))*|s-t|^β:=by
    rw [←Finset.sum_mul,←Finset.mul_sum]
  rw [hsum] at hp
  change |initial L k p g (x+s • d)*(∏j,leaves L k p g j (x+s • d))-
    initial L k p g (x+t • d)*(∏j,leaves L k p g j (x+t • d))|≤_
  convert hp using 1 <;> dsimp only [C] <;> ring

end SHE.PhysicalChainArrays
