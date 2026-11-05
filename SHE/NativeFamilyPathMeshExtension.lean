module
public import SHE.NativePathMeshExtension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeFamilyPathMeshExtension
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory
variable{ι:Type*}(Ω:ι→Type*)[∀i,MeasurableSpace (Ω i)]
variable{E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
  [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)]
variable(X:∀i,ℝ≥0→Ω i→E)
variable(hc:∀i ω,Continuous (fun t=>X i t ω))
variable(hX:∀i,Measurable (Function.uncurry (X i)))

include hX in
/-- The family prefix law is proved before the local callback is invoked
at each mesh step. Only genuine future STATE kernels given the actual
STATE prefix occur in the callback. -/
theorem finite_mesh(h:ℝ≥0)(N:ℕ)
    (hinitial:∀i j, (μ i).map (NativeContinuousPath.path 0 (X i) (hc i))=
      (μ j).map (NativeContinuousPath.path 0 (X j) (hc j)))
    (hfuture:∀n:ℕ,n<N→
      (∀i j,(μ i).map (NativeContinuousPath.path ((n:ℝ≥0)*h) (X i) (hc i))=
        (μ j).map (NativeContinuousPath.path ((n:ℝ≥0)*h) (X j) (hc j)))→
      ∀i j,condDistrib
        (NativeContinuousPath.path h (fun t ω=>X i ((n:ℝ≥0)*h+t) ω)
          (NativePathRestrictionClock.shifted_continuous ((n:ℝ≥0)*h) (X i) (hc i)))
        (NativeContinuousPath.path ((n:ℝ≥0)*h) (X i) (hc i)) (μ i)
        =ᵐ[(μ i).map (NativeContinuousPath.path ((n:ℝ≥0)*h) (X i) (hc i))]
        condDistrib
        (NativeContinuousPath.path h (fun t ω=>X j ((n:ℝ≥0)*h+t) ω)
          (NativePathRestrictionClock.shifted_continuous ((n:ℝ≥0)*h) (X j) (hc j)))
        (NativeContinuousPath.path ((n:ℝ≥0)*h) (X j) (hc j)) (μ j)):
    ∀i j,(μ i).map (NativeContinuousPath.path ((N:ℝ≥0)*h) (X i) (hc i))=
      (μ j).map (NativeContinuousPath.path ((N:ℝ≥0)*h) (X j) (hc j)):=by
  have hi:∀n:ℕ,n≤N→∀i j,
      (μ i).map (NativeContinuousPath.path ((n:ℝ≥0)*h) (X i) (hc i))=
      (μ j).map (NativeContinuousPath.path ((n:ℝ≥0)*h) (X j) (hc j)):=by
    intro n
    induction n with
    | zero=>
      intro _ i j
      have hz:((0:ℕ):ℝ≥0)*h=0:=by simp
      rw [hz]
      exact hinitial i j
    | succ n ih=>
      intro hn
      have hp:=ih (Nat.le_of_succ_le hn)
      have hf:=hfuture n (Nat.lt_of_succ_le hn) hp
      intro i j
      have he:=NativePathMeshExtension.step (μ i) (μ j) (X i) (X j) (hc i) (hc j)
        (hX i) (hX j) ((n:ℝ≥0)*h) h (hp i j) (hf i j)
      have hs:((n+1:ℕ):ℝ≥0)*h=(n:ℝ≥0)*h+h:=by simp [Nat.cast_add,add_mul]
      rw [hs]
      exact he
  exact hi N le_rfl

include hX in
/-- A common finite mesh is chosen internally. The actual local kernel
comparison may depend on equality of ALL family prefix laws, which the
induction establishes before each callback. No Markov, restart or weak
uniqueness assertion is assumed by this path geometry theorem. -/
theorem arbitrary_horizon(T window:ℝ≥0)(hwindow:0<window)
    (hinitial:∀i j,(μ i).map (NativeContinuousPath.path 0 (X i) (hc i))=
      (μ j).map (NativeContinuousPath.path 0 (X j) (hc j)))
    (hfuture:∀v h:ℝ≥0,0<h→h≤window→v+h≤T→
      (∀i j,(μ i).map (NativeContinuousPath.path v (X i) (hc i))=
        (μ j).map (NativeContinuousPath.path v (X j) (hc j)))→
      ∀i j,condDistrib
        (NativeContinuousPath.path h (fun t ω=>X i (v+t) ω)
          (NativePathRestrictionClock.shifted_continuous v (X i) (hc i)))
        (NativeContinuousPath.path v (X i) (hc i)) (μ i)
        =ᵐ[(μ i).map (NativeContinuousPath.path v (X i) (hc i))]
        condDistrib
        (NativeContinuousPath.path h (fun t ω=>X j (v+t) ω)
          (NativePathRestrictionClock.shifted_continuous v (X j) (hc j)))
        (NativeContinuousPath.path v (X j) (hc j)) (μ j)):
    ∀i j,(μ i).map (NativeContinuousPath.path T (X i) (hc i))=
      (μ j).map (NativeContinuousPath.path T (X j) (hc j)):=by
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
  have he:=finite_mesh Ω μ X hc hX δ N hinitial (fun n hn hp=>by
    apply hfuture ((n:ℝ≥0)*δ) δ hδ hδw
    · calc
        (n:ℝ≥0)*δ+δ=((n+1:ℕ):ℝ≥0)*δ:=by
          simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
        _≤(N:ℝ≥0)*δ:=mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.succ_le_of_lt hn) (show (0:ℝ≥0)≤δ from bot_le)
        _=T:=htotal
    · exact hp)
  rw [htotal] at he
  exact he
end SHE.NativeFamilyPathMeshExtension
