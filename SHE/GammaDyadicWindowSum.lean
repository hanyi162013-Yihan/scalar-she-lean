module
public import SHE.GammaDyadicWindowScale
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace SHE.GammaDyadicWindowSum
open Real GammaDyadicWindowScale

/-- The high positive dyadic bands of the complete Gamma estimate are
absolutely summable with EXACT actual dyadic windows. The resulting
three rows are the Gamma contribution to the finite master. -/
theorem norm_sum {E:Type*}[NormedAddCommGroup E][CompleteSpace E]
    {β ρ C K m:ℝ}(hβ:0<β)(hα:0<GammaDyadicWindowScale.alpha β ρ)(hα1:GammaDyadicWindowScale.alpha β ρ<1)
    (hq:0<GammaDyadicWindowScale.degree β ρ)(hC:0≤C)(hK:0≤K)(hm:0≤m)(J:ℕ)(x:ℕ→E)
    (hbound:∀n,‖x n‖^2≤C*(CompactMollifier.radius (J+n)^(2*β)*K^2+
      CompactMollifier.radius (J+n)^(2*β+4*ρ)*
        ((RemainderBandSpans.span β (J+n):ℝ)^((β-1)/2)*m^2+
          min 1 (m^2/CompactMollifier.radius (J+n)^2)))):
    Summable x ∧ ‖∑'n,x n‖≤sqrt C*(
      StateBands.geometricConstant β*((2:ℝ)^J)^(-β)*K+
      StateBands.rootConstant (GammaDyadicWindowScale.alpha β ρ)*m^(GammaDyadicWindowScale.alpha β ρ)+
      StateBands.geometricConstant (GammaDyadicWindowScale.degree β ρ)*((2:ℝ)^J)^(-GammaDyadicWindowScale.degree β ρ)*m):=by
  let R:ℝ:=(2:ℝ)^J
  have hR:0<R:=by dsimp[R];positivity
  let f:ℕ→ℝ:=fun n=>(R*(2:ℝ)^n)^(-β)*K
  let g:ℕ→ℝ:=fun n=>(R*(2:ℝ)^n)^(-GammaDyadicWindowScale.alpha β ρ)*min 1 (m*(R*(2:ℝ)^n))
  let h:ℕ→ℝ:=fun n=>(R*(2:ℝ)^n)^(-GammaDyadicWindowScale.degree β ρ)*m
  have hf:Summable f:=(StateBands.geometric_bands hβ hR).1.mul_right K
  have hg:Summable g:=(StateBands.scaled_root_bands hα hα1 hm hR).1
  have hh:Summable h:=(StateBands.geometric_bands hq hR).1.mul_right m
  have hmajor:Summable (fun n=>sqrt C*(f n+g n+h n)):=((hf.add hg).add hh).mul_left (sqrt C)
  have hx(n:ℕ):‖x n‖≤sqrt C*(f n+g n+h n):=by
    have he:=GammaDyadicWindowScale.norm_of_squared hC hK hm (J+n) (x n) (hbound n)
    simpa only [f,g,h,R,pow_add] using he
  have hs:Summable x:=Summable.of_norm_bounded hmajor hx
  refine ⟨hs,?_⟩
  have hfval:(∑'n,f n)=StateBands.geometricConstant β*R^(-β)*K:=by
    rw [show f=(fun n=>(R*(2:ℝ)^n)^(-β)*K) from rfl,tsum_mul_right,
      (StateBands.geometric_bands hβ hR).2]
  have hhval:(∑'n,h n)=StateBands.geometricConstant (GammaDyadicWindowScale.degree β ρ)*R^(-GammaDyadicWindowScale.degree β ρ)*m:=by
    rw [show h=(fun n=>(R*(2:ℝ)^n)^(-GammaDyadicWindowScale.degree β ρ)*m) from rfl,tsum_mul_right,
      (StateBands.geometric_bands hq hR).2]
  calc
    _≤∑'n,sqrt C*(f n+g n+h n):=tsum_of_norm_bounded hmajor.hasSum hx
    _=sqrt C*((∑'n,f n)+(∑'n,g n)+(∑'n,h n)):=by
      rw [tsum_mul_left,(hf.add hg).tsum_add hh,hf.tsum_add hg]
    _≤sqrt C*(StateBands.geometricConstant β*R^(-β)*K+
        StateBands.rootConstant (GammaDyadicWindowScale.alpha β ρ)*m^(GammaDyadicWindowScale.alpha β ρ)+
        StateBands.geometricConstant (GammaDyadicWindowScale.degree β ρ)*R^(-GammaDyadicWindowScale.degree β ρ)*m):=by
      rw [hfval,hhval]
      have hgval:(∑'n,g n)≤StateBands.rootConstant (GammaDyadicWindowScale.alpha β ρ)*
          m^(GammaDyadicWindowScale.alpha β ρ):=
        (StateBands.scaled_root_bands hα hα1 hm hR).2
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg C)
      linarith
    _=_:=rfl

/-- The printed positive-beta family gives precisely R^-beta K,
m^GammaDyadicWindowScale.alpha, and R^-qGamma m, with N fixed independently elsewhere. No
recursion-depth or coefficient approximation limit is used here. -/
theorem printed_parameters {E:Type*}[NormedAddCommGroup E][CompleteSpace E]
    {β C K m:ℝ}(hβ:0<β)(hβsmall:β≤4/25)(hC:0≤C)(hK:0≤K)(hm:0≤m)
    (J:ℕ)(x:ℕ→E)
    (hbound:∀n,‖x n‖^2≤C*(CompactMollifier.radius (J+n)^(2*β)*K^2+
      CompactMollifier.radius (J+n)^(2*β+4*SHE.rho β)*
        ((RemainderBandSpans.span β (J+n):ℝ)^((β-1)/2)*m^2+
          min 1 (m^2/CompactMollifier.radius (J+n)^2)))):
    Summable x ∧ ‖∑'n,x n‖≤sqrt C*(
      StateBands.geometricConstant β*((2:ℝ)^J)^(-β)*K+
      StateBands.rootConstant (SHE.alpha β)*m^(SHE.alpha β)+
      StateBands.geometricConstant (SHE.qGamma β)*((2:ℝ)^J)^(-SHE.qGamma β)*m):=by
  have had:=SHE.admissible_parameters β hβ hβsmall
  have hα0:0<GammaDyadicWindowScale.alpha β (SHE.rho β):=had.2.2.2.2.1
  have hα1:GammaDyadicWindowScale.alpha β (SHE.rho β)<1:=had.2.2.2.2.2.1
  have hq:0<GammaDyadicWindowScale.degree β (SHE.rho β):=by
    rw [degree_eq]
    exact (SHE.all_degrees_positive β hβ hβsmall).1
  simpa only [degree_eq,show GammaDyadicWindowScale.alpha β (SHE.rho β)=SHE.alpha β from rfl] using
    norm_sum hβ hα0 hα1 hq hC hK hm J x hbound
end SHE.GammaDyadicWindowSum
