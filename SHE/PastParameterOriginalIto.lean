module

public import SHE.PastParameterDiagonal
public import SHE.TerminalItoClosedLimit
public import SHE.StandardTerminalPastLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.PastParameterOriginalIto
open Set Filter MeasureTheory PredictableL2 PastItoInputs Topology Classical
open scoped NNReal ENNReal
variable {Ω X C:Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H v:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- Finite simple past substitution preserves the SAME original Ito
driver by ordinary event pullout. No random-reference formula is assumed. -/
theorem simple_input (hlocal:StandardTerminalPastLocality J)
    (K:X→Ω→ℝ)
    (hrep:∀x,∃input:Process (E:=C) 𝓕 μ H,
      J.integral (post 𝓕 μ H v input)=ᵐ[μ] K x)
    (s:@SimpleFunc Ω (𝓕 v) X):
    ∃input:Process (E:=C) 𝓕 μ H,J.integral input=ᵐ[μ] fun ω=>K (s ω) ω:=by
  choose input hi using hrep
  let A:=fun x:X=>{ω|s ω=x}
  have hA(x:X):MeasurableSet[𝓕 v] (A x):=@SimpleFunc.measurableSet_fiber Ω X (𝓕 v) s x
  let S:=@SimpleFunc.range Ω X (𝓕 v) s
  let U:=fun x:X=>eventProcess 𝓕 μ H v (A x) (hA x) (input x)
  have he(x:X):J.integral (U x)=ᵐ[μ] (A x).indicator (K x):=by
    filter_upwards [hlocal v (A x) (hA x) (input x),hi x] with ω hω hK
    change J.integral (U x) ω=_
    rw [hω]
    by_cases ha:ω∈A x
    · simp only [indicator_of_mem ha,hK]
    · simp only [indicator_of_notMem ha]
  refine ⟨∑x∈S,U x,?_⟩
  have hs:J.integral (∑x∈S,U x)=∑x∈S,J.integral (U x):=map_sum J.integral U S
  have hsa:=Lp.coeFn_fun_finsetSum S (fun x=>J.integral (U x))
  rw [←hs] at hsa
  have hae:∀ᵐω∂μ,∀x∈S,J.integral (U x) ω=(A x).indicator (K x) ω:=
    (Finset.eventually_all S).mpr (fun x _=>he x)
  filter_upwards [hae,hsa] with ω hω hsum
  rw [hsum]
  calc
    _=∑x∈S,(A x).indicator (K x) ω:=Finset.sum_congr rfl (fun x hx=>hω x hx)
    _=(A (s ω)).indicator (K (s ω)) ω:=by
      apply Finset.sum_eq_single (s ω)
      · intro x hx hne
        have hneq:s ω≠x:=Ne.symm hne
        simp only [A,Set.indicator,mem_setOf_eq,hneq,ite_false]
      · exact fun hn=>(hn (@SimpleFunc.mem_range_self Ω X (𝓕 v) s ω)).elim
    _=K (s ω) ω:=indicator_of_mem (show ω∈A (s ω) from rfl) _

/-- A continuous uniformly bounded finite-Ito family admits an ORIGINAL
J witness after genuine F_v-random parameter substitution. The proof uses
finite simple past approximation and strong L2 closed-range passage. -/
theorem random_input (hlocal:StandardTerminalPastLocality J)
    (K:X→Ω→ℝ) (hK:∀x,Measurable (K x))
    (hc:∀ω,Continuous (fun x=>K x ω)) {B:ℝ} (hB:0≤B) (hb:∀x ω,‖K x ω‖≤B)
    (hrep:∀x,∃input:Process (E:=C) 𝓕 μ H,
      J.integral (post 𝓕 μ H v input)=ᵐ[μ] K x)
    {u:Ω→X} (hu:StronglyMeasurable[𝓕 v] u):
    ∃input:Process (E:=C) 𝓕 μ H,J.integral input=ᵐ[μ] fun ω=>K (u ω) ω:=by
  let F:=fun n:ℕ=>fun ω=>K ((hu.approx n) ω) ω
  let G:=fun ω=>K (u ω) ω
  have hm(n:ℕ):Measurable (F n):=
    PastParameterSectionExpectation.simple_eval_measurable (𝓕 v) (𝓕.le v) K hK (hu.approx n)
  have hgm:StronglyMeasurable G:=
    PastParameterDiagonal.stronglyMeasurable_diagonal (𝓕 v) (𝓕.le v) K hK hu hc
  have hg:MemLp G 2 μ:=MemLp.of_bound hgm.aestronglyMeasurable B
    (Eventually.of_forall (fun ω=>hb (u ω) ω))
  have hex(n:ℕ):∃input:Process (E:=C) 𝓕 μ H,J.integral input=ᵐ[μ] F n:=
    simple_input 𝓕 μ H v J hlocal K hrep (hu.approx n)
  choose input hi using hex
  have hlim:Tendsto (fun n=>∫ω,‖F n ω-G ω‖^2 ∂μ) atTop (𝓝 0):=by
    have ht:=tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun _=>(2*B)^2)
      (Eventually.of_forall (fun n=>((hm n).sub hgm.measurable).norm.pow_const 2 |>.aestronglyMeasurable))
      (Eventually.of_forall (fun n=>Eventually.of_forall (fun ω=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hn:=norm_sub_le (F n ω) (G ω)
        have hle:‖F n ω-G ω‖≤2*B:=hn.trans (by dsimp only [F,G];linarith [hb ((hu.approx n) ω) ω,hb (u ω) ω])
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2)))
      (integrable_const _)
      (Eventually.of_forall (fun ω=>by
        have ht:=((((hc ω).tendsto (u ω)).comp (hu.tendsto_approx ω)).sub_const (G ω)).norm.pow 2
        simpa only [F,G,Function.comp_def,Pi.sub_apply,sub_self,norm_zero,zero_pow (by norm_num:2≠0)] using ht))
    simpa only [Pi.sub_apply,integral_zero] using ht
  exact TerminalItoClosedLimit.original_input 𝓕 μ H J input F G hg hi hlim

end SHE.PastParameterOriginalIto
