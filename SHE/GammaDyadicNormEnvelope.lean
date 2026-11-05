module
public import SHE.GammaDyadicWindowSum
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SHE.GammaDyadicNormEnvelope
open Real
/-- The three genuine unsquared Gamma rows form an absolutely summable
majorant. This applies equally to actual band RMS norms or to coherent
Banach-valued band outputs. -/
theorem sum_bound {E:Type*}[NormedAddCommGroup E][CompleteSpace E]
    {β α q C K m:ℝ}(hβ:0<β)(hα:0<α)(hα1:α<1)(hq:0<q)
    (hC:0≤C)(hK:0≤K)(hm:0≤m)(J:ℕ)(x:ℕ→E)
    (hbound:∀n,‖x n‖≤C*(((2:ℝ)^(J+n))^(-β)*K+
      ((2:ℝ)^(J+n))^(-α)*min 1 (m*(2:ℝ)^(J+n))+
      ((2:ℝ)^(J+n))^(-q)*m)):
    Summable x ∧ ‖∑'n,x n‖≤C*(StateBands.geometricConstant β*((2:ℝ)^J)^(-β)*K+
      StateBands.rootConstant α*m^α+StateBands.geometricConstant q*((2:ℝ)^J)^(-q)*m):=by
  let R:ℝ:=(2:ℝ)^J
  have hR:0<R:=by dsimp[R];positivity
  let f:ℕ→ℝ:=fun n=>(R*(2:ℝ)^n)^(-β)*K
  let g:ℕ→ℝ:=fun n=>(R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n))
  let h:ℕ→ℝ:=fun n=>(R*(2:ℝ)^n)^(-q)*m
  have hf:Summable f:=(StateBands.geometric_bands hβ hR).1.mul_right K
  have hg:Summable g:=(StateBands.scaled_root_bands hα hα1 hm hR).1
  have hh:Summable h:=(StateBands.geometric_bands hq hR).1.mul_right m
  have hmajor:Summable (fun n=>C*(f n+g n+h n)):=((hf.add hg).add hh).mul_left C
  have hx(n:ℕ):‖x n‖≤C*(f n+g n+h n):=by
    simpa only [f,g,h,R,pow_add] using hbound n
  refine ⟨Summable.of_norm_bounded hmajor hx,?_⟩
  have hfval:(∑'n,f n)=StateBands.geometricConstant β*R^(-β)*K:=by
    rw [show f=(fun n=>(R*(2:ℝ)^n)^(-β)*K) from rfl,tsum_mul_right,(StateBands.geometric_bands hβ hR).2]
  have hhval:(∑'n,h n)=StateBands.geometricConstant q*R^(-q)*m:=by
    rw [show h=(fun n=>(R*(2:ℝ)^n)^(-q)*m) from rfl,tsum_mul_right,(StateBands.geometric_bands hq hR).2]
  have hgval:(∑'n,g n)≤StateBands.rootConstant α*m^α:=(StateBands.scaled_root_bands hα hα1 hm hR).2
  calc
    _≤∑'n,C*(f n+g n+h n):=tsum_of_norm_bounded hmajor.hasSum hx
    _=C*((∑'n,f n)+(∑'n,g n)+(∑'n,h n)):=by
      rw [tsum_mul_left,(hf.add hg).tsum_add hh,hf.tsum_add hg]
    _≤C*(StateBands.geometricConstant β*R^(-β)*K+
      StateBands.rootConstant α*m^α+StateBands.geometricConstant q*R^(-q)*m):=by
      rw [hfval,hhval]
      apply mul_le_mul_of_nonneg_left _ hC
      linarith
    _=_:=rfl
end SHE.GammaDyadicNormEnvelope
