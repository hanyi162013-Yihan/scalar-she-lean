module

public import SHE.DefectBlockCost
public import SHE.PhysicalTerminalHeat

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace SHE.StoppedFullDefectCost
open Real
open scoped BigOperators

/-- The full physical trace product reduces to the sum of its actual
ordered age-pair costs BEFORE new-time integration. -/
theorem cost (K θ ell W B Csigned ρ:ℝ)(hK:0≤K)(hθ:0<θ)
    (hell:0<ell)(hW:0≤W)(hB:1≤B)(hSigned:0≤Csigned)(n:ℕ):
    ∃C:ℝ,0<C ∧ ∀{g:ℕ},g≤n→∀Λ:ℝ,1≤Λ→
      ∀d:Fin g→ℝ,(∀i,0<d i)→∀G E:ℝ,0≤G→0≤E→
      let X:=fun i:Fin g=>
        ((max B 8*min 1 (Λ*d i)^2/d i)/(ell/2))*K*sqrt B*sqrt (d i/(4*Real.pi^2))*Csigned*
          (Λ^ρ*(θ*(d i/(4*Real.pi^2)))^(-(1/2:ℝ))+
            (θ*(d i/(4*Real.pi^2)))^(-(1/2:ℝ)-ρ))
      let Y:=fun i:Fin g=>(max B 8/d i)/(ell/2)*(4*W*(n:ℝ))
      Λ^(-ρ/2)*sqrt ((9/4:ℝ)*G^2*((g:ℝ)*∑j,Y j)*((g:ℝ)*(∑i,X i)*E))≤
        C*G*sqrt E*(∑i:Fin g,∑j:Fin g,
          min 1 (Λ*d i)*(d i)^(-(1/2:ℝ))*(d j)^(-(1/2:ℝ))*
            (1+Λ^(-ρ/2)*(d i)^(-ρ/2))):=by
  obtain ⟨C0,hC0,hcost⟩:=DefectBlockCost.cost K θ ell ell W B Csigned ρ hK hθ hell hell hW hB hSigned n
  let C:=1+(3/2:ℝ)*(n:ℝ)*C0
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro g hgn Λ hΛ d hd G E hG hE X Y
  have hΛp:0<Λ:=zero_lt_one.trans_le hΛ
  have hX(i:Fin g):0≤X i:=by have hi:=hd i;dsimp [X];positivity
  have hY(i:Fin g):0≤Y i:=by have hi:=hd i;dsimp [Y];positivity
  let T:=∑i:Fin g,∑j:Fin g,X i*Y j
  have hT:0≤T:=Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>mul_nonneg (hX i) (hY j)))
  have he:(9/4:ℝ)*G^2*((g:ℝ)*∑j,Y j)*((g:ℝ)*(∑i,X i)*E)=
      ((3/2:ℝ)*(g:ℝ)*G*sqrt E)^2*T:=by
    rw [mul_pow,mul_pow,mul_pow,sq_sqrt hE]
    dsimp only [T]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs:sqrt ((9/4:ℝ)*G^2*((g:ℝ)*∑j,Y j)*((g:ℝ)*(∑i,X i)*E))=
      ((3/2:ℝ)*(g:ℝ)*G*sqrt E)*sqrt T:=by
    rw [he,sqrt_mul (sq_nonneg _),sqrt_sq (by positivity)]
  have hsum:sqrt T≤∑i:Fin g,∑j:Fin g,sqrt (X i*Y j):=by
    exact (PhysicalFirstScore.sqrt_sum_le _ (fun i=>Finset.sum_nonneg
      (fun j _=>mul_nonneg (hX i) (hY j)))).trans
      (Finset.sum_le_sum (fun i _=>PhysicalFirstScore.sqrt_sum_le _
        (fun j=>mul_nonneg (hX i) (hY j))))
  have hpair(i j:Fin g):Λ^(-ρ/2)*sqrt (X i*Y j)≤
      C0*(min 1 (Λ*d i)*(d i)^(-(1/2:ℝ))*(d j)^(-(1/2:ℝ))*
        (1+Λ^(-ρ/2)*(d i)^(-ρ/2))):=by
    have hh:=hcost Λ (d i) (d j) hΛ (hd i) (hd j)
    convert hh using 1
    · congr 1
      congr 1
      dsimp only [X,Y]
      ring
    · ring
  have hp:Λ^(-ρ/2)*sqrt T≤C0*(∑i:Fin g,∑j:Fin g,
      min 1 (Λ*d i)*(d i)^(-(1/2:ℝ))*(d j)^(-(1/2:ℝ))*
        (1+Λ^(-ρ/2)*(d i)^(-ρ/2))):=by
    apply (mul_le_mul_of_nonneg_left hsum (rpow_nonneg hΛp.le _)).trans
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hpair i j))
  have hcoeff:(3/2:ℝ)*(g:ℝ)*C0≤C:=by
    have hn:(g:ℝ)≤(n:ℝ):=by exact_mod_cast hgn
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num:0≤(3/2:ℝ))) hC0.le
    dsimp [C]
    linarith
  have hsum0:0≤∑i:Fin g,∑j:Fin g,
      min 1 (Λ*d i)*(d i)^(-(1/2:ℝ))*(d j)^(-(1/2:ℝ))*
        (1+Λ^(-ρ/2)*(d i)^(-ρ/2)):=by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    have hi:=hd i;have hj:=hd j
    positivity
  rw [hs]
  have hh:=mul_le_mul_of_nonneg_left hp
    (show 0≤(3/2:ℝ)*(g:ℝ)*G*sqrt E by positivity)
  apply (show Λ^(-ρ/2)*(((3/2:ℝ)*(g:ℝ)*G*sqrt E)*sqrt T)≤
      ((3/2:ℝ)*(g:ℝ)*C0)*G*sqrt E*(∑i:Fin g,∑j:Fin g,
        min 1 (Λ*d i)*(d i)^(-(1/2:ℝ))*(d j)^(-(1/2:ℝ))*
          (1+Λ^(-ρ/2)*(d i)^(-ρ/2))) from by convert hh using 1 <;> ring).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hG) (sqrt_nonneg E)) hsum0

end SHE.StoppedFullDefectCost
