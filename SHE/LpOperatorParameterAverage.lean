module
public import SHE.TerminalItoFubini
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace SHE.LpOperatorParameterAverage
open MeasureTheory
open scoped ENNReal InnerProductSpace

theorem integrable_inner {P C:Type*} [MeasurableSpace P]
    [NormedAddCommGroup C][InnerProductSpace ℝ C]{ν:Measure P}
    {f g:P→C}(hf:MemLp f 2 ν)(hg:MemLp g 2 ν):
    Integrable (fun p=>inner ℝ (f p) (g p)) ν:=by
  apply (L2.integrable_inner (𝕜:=ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with p hf hg
  rw [hf,hg]

variable {X P Ω C:Type*} [MeasurableSpace X][MeasurableSpace P][MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][CompleteSpace C]
variable (η:Measure X)[IsFiniteMeasure η](ν:Measure P)[IsFiniteMeasure ν]
variable (μ:Measure Ω)[IsFiniteMeasure μ]

/-- Joint L2 representatives commute with a bounded L2 operator under
parameter averaging, without assuming separability of the probability
L2 space or measurability of the parameter map into that space. The
proof uses the actual Hilbert adjoint and ordinary scalar Fubini. -/
theorem commutes (T:Lp C 2 ν→L[ℝ]Lp ℝ 2 μ)
    (K:X→Lp C 2 ν)(raw:X×P→C)(hraw:MemLp raw 2 (η.prod ν))
    (hK:∀x,K x=ᵐ[ν] fun p=>raw (x,p))
    (Y:X×Ω→ℝ)(hY:MemLp Y 2 (η.prod μ))
    (hRep:∀ᵐx∂η,T (K x)=ᵐ[μ] fun ω=>Y (x,ω))
    (Kavg:Lp C 2 ν)(hKa:Kavg=ᵐ[ν] fun p=>∫x,raw (x,p) ∂η)
    (Yavg:Lp ℝ 2 μ)(hYa:Yavg=ᵐ[μ] fun ω=>∫x,Y (x,ω) ∂η):
    T Kavg=Yavg:=by
  apply ext_inner_right ℝ
  intro Z
  let A:=T.adjoint Z
  have hiR:Integrable (fun z:X×P=>inner ℝ (raw z) (A z.2)) (η.prod ν):=
    integrable_inner hraw ((Lp.memLp A).comp_snd η)
  have hiY:Integrable (fun z:X×Ω=>Y z*Z z.2) (η.prod μ):=by
    simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using
      integrable_inner hY ((Lp.memLp Z).comp_snd η)
  have hrsections:∀ᵐp∂ν,Integrable (fun x=>raw (x,p)) η:=
    (hraw.integrable (by norm_num : (1:ENNReal)≤2)).prod_left_ae
  calc
    inner ℝ (T Kavg) Z=inner ℝ Kavg A:=(T.adjoint_inner_right Kavg Z).symm
    _=∫p,inner ℝ (Kavg p) (A p) ∂ν:=L2.inner_def _ _
    _=∫p,∫x,inner ℝ (raw (x,p)) (A p) ∂η ∂ν:=by
      apply integral_congr_ae
      filter_upwards [hKa,hrsections] with p hp hi
      rw [hp]
      simpa only [real_inner_comm,innerSL_apply_apply] using
        ((innerSL ℝ (A p)).integral_comp_comm hi).symm
    _=∫x,∫p,inner ℝ (raw (x,p)) (A p) ∂ν ∂η:=(integral_integral_swap hiR).symm
    _=∫x,inner ℝ (K x) A ∂η:=by
      apply integral_congr_ae
      filter_upwards with x
      rw [L2.inner_def]
      exact integral_congr_ae ((hK x).mono (fun p hp=>congrArg (fun v=>inner ℝ v (A p)) hp.symm))
    _=∫x,inner ℝ (T (K x)) Z ∂η:=by
      apply integral_congr_ae
      filter_upwards with x
      exact T.adjoint_inner_right (K x) Z
    _=∫x,∫ω,Y (x,ω)*Z ω ∂μ ∂η:=by
      apply integral_congr_ae
      filter_upwards [hRep] with x hx
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hx] with ω hω
      simp only [hω,RCLike.inner_apply,conj_trivial,mul_comm]
    _=∫ω,∫x,Y (x,ω)*Z ω ∂η ∂μ:=integral_integral_swap hiY
    _=inner ℝ Yavg Z:=by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hYa] with ω hω
      rw [hω,integral_mul_const]
      simp only [RCLike.inner_apply,conj_trivial,mul_comm]
end SHE.LpOperatorParameterAverage
