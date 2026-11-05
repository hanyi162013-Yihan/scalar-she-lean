module
public import SHE.NativePathRestrictionClock
public import SHE.ConditionalStateProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativePathMeshExtension
open Set MeasureTheory ProbabilityTheory ContinuousPathRestriction
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory
variable {Ω Ω' E:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
  [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (μ:Measure Ω)(ν:Measure Ω')[IsFiniteMeasure μ][IsFiniteMeasure ν]
variable (X:ℝ≥0→Ω→E)(Y:ℝ≥0→Ω'→E)
variable (hc:∀ω,Continuous (fun t=>X t ω))(hd:∀ω,Continuous (fun t=>Y t ω))
variable (hX:Measurable (Function.uncurry X))(hY:Measurable (Function.uncurry Y))

include hX hY in
/-- One actual state-path extension, conditioning on the state PREFIX
and comparing only the future STATE path distribution. -/
theorem step(v h:ℝ≥0)
    (hprefix:μ.map (NativeContinuousPath.path v X hc)=ν.map (NativeContinuousPath.path v Y hd))
    (hfuture:condDistrib
      (NativeContinuousPath.path h (fun t ω=>X (v+t) ω) (NativePathRestrictionClock.shifted_continuous v X hc))
      (NativeContinuousPath.path v X hc) μ
      =ᵐ[μ.map (NativeContinuousPath.path v X hc)]
      condDistrib
      (NativeContinuousPath.path h (fun t ω=>Y (v+t) ω) (NativePathRestrictionClock.shifted_continuous v Y hd))
      (NativeContinuousPath.path v Y hd) ν):
    μ.map (NativeContinuousPath.path (v+h) X hc)=ν.map (NativeContinuousPath.path (v+h) Y hd):=by
  apply ConditionalContinuousPathExtension.processes v h μ ν X Y hc hd hX hY
  · simpa only [NativePathRestrictionClock.past_path] using hprefix
  · simpa only [NativePathRestrictionClock.past_path,NativePathRestrictionClock.future_path] using hfuture

include hX hY in
/-- Finite equal-mesh induction for actual state path laws. Every
conditional kernel is the genuine future STATE kernel given the actual
state prefix; no joint state/noise-prefix law is assumed. -/
theorem finite_mesh(h:ℝ≥0)(N:ℕ)
    (hinitial:μ.map (NativeContinuousPath.path 0 X hc)=ν.map (NativeContinuousPath.path 0 Y hd))
    (hfuture:∀n:ℕ,n<N→condDistrib
      (NativeContinuousPath.path h (fun t ω=>X ((n:ℝ≥0)*h+t) ω)
        (NativePathRestrictionClock.shifted_continuous ((n:ℝ≥0)*h) X hc))
      (NativeContinuousPath.path ((n:ℝ≥0)*h) X hc) μ
      =ᵐ[μ.map (NativeContinuousPath.path ((n:ℝ≥0)*h) X hc)]
      condDistrib
      (NativeContinuousPath.path h (fun t ω=>Y ((n:ℝ≥0)*h+t) ω)
        (NativePathRestrictionClock.shifted_continuous ((n:ℝ≥0)*h) Y hd))
      (NativeContinuousPath.path ((n:ℝ≥0)*h) Y hd) ν):
    μ.map (NativeContinuousPath.path ((N:ℝ≥0)*h) X hc)=
      ν.map (NativeContinuousPath.path ((N:ℝ≥0)*h) Y hd):=by
  have hi:∀n:ℕ,n≤N→μ.map (NativeContinuousPath.path ((n:ℝ≥0)*h) X hc)=
      ν.map (NativeContinuousPath.path ((n:ℝ≥0)*h) Y hd):=by
    intro n
    induction n with
    | zero=>
      intro _
      have hz:((0:ℕ):ℝ≥0)*h=0:=by simp
      rw [hz]
      exact hinitial
    | succ n ih=>
      intro hn
      have he:=step μ ν X Y hc hd hX hY ((n:ℝ≥0)*h) h (ih (Nat.le_of_succ_le hn))
        (hfuture n (Nat.lt_of_succ_le hn))
      have hs:((n+1:ℕ):ℝ≥0)*h=(n:ℝ≥0)*h+h:=by simp [Nat.cast_add,add_mul]
      rw [hs]
      exact he
  exact hi N le_rfl

include hX hY in
/-- A finite equal mesh reaches any prescribed finite horizon. Its step
size is chosen internally below the available local interval, and only
actual state-prefix conditional future-state kernels are used. -/
theorem arbitrary_horizon(T window:ℝ≥0)(hwindow:0<window)
    (hinitial:μ.map (NativeContinuousPath.path 0 X hc)=ν.map (NativeContinuousPath.path 0 Y hd))
    (hfuture:∀v h:ℝ≥0,0<h→h≤window→v+h≤T→condDistrib
      (NativeContinuousPath.path h (fun t ω=>X (v+t) ω)
        (NativePathRestrictionClock.shifted_continuous v X hc))
      (NativeContinuousPath.path v X hc) μ
      =ᵐ[μ.map (NativeContinuousPath.path v X hc)]
      condDistrib
      (NativeContinuousPath.path h (fun t ω=>Y (v+t) ω)
        (NativePathRestrictionClock.shifted_continuous v Y hd))
      (NativeContinuousPath.path v Y hd) ν):
    μ.map (NativeContinuousPath.path T X hc)=ν.map (NativeContinuousPath.path T Y hd):=by
  by_cases hT:T=0
  · subst T
    exact hinitial
  have hTp:0<T:=pos_iff_ne_zero.mpr hT
  obtain ⟨N,hN⟩:=exists_nat_gt (T/window)
  have hNp:0<(N:ℝ≥0):=lt_of_le_of_lt (show (0:ℝ≥0)≤T/window from bot_le) hN
  let δ:ℝ≥0:=T/(N:ℝ≥0)
  have hδ:0<δ:=div_pos hTp hNp
  have hcap:T≤(N:ℝ≥0)*window:=(div_le_iff₀ hwindow).mp hN.le
  have hδw:δ≤window:=by
    apply (div_le_iff₀ hNp).mpr
    simpa only [mul_comm] using hcap
  have htotal:(N:ℝ≥0)*δ=T:=by
    dsimp [δ]
    exact mul_div_cancel₀ T (ne_of_gt hNp)
  have he:=finite_mesh μ ν X Y hc hd hX hY δ N hinitial (fun n hn=>by
    apply hfuture ((n:ℝ≥0)*δ) δ hδ hδw
    calc
      (n:ℝ≥0)*δ+δ=((n+1:ℕ):ℝ≥0)*δ:=by simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      _≤(N:ℝ≥0)*δ:=mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hn) (show (0:ℝ≥0)≤δ from bot_le)
      _=T:=htotal)
  rw [htotal] at he
  exact he
end SHE.NativePathMeshExtension
