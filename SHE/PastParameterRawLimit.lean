module

public import SHE.TerminalItoRawLimit
public import SHE.PastSimpleItoSelection
public import SHE.PastParameterDiagonal
public import SHE.TerminalItoClosedLimit
public import SHE.StandardTerminalPastLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.PastParameterRawLimit
open Set Filter MeasureTheory PredictableL2 PastItoInputs Topology Classical
open scoped NNReal ENNReal
variable {Ω X C:Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H v:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- Exact random-past raw-input substitution through finite simple
selection and strong original-Ito closure. Uniform boundedness is needed
only for the actual scalar terminal residual, not pointwise on all
parameter-dependent stochastic inputs. -/
theorem original_input (hlocal:StandardTerminalPastLocality J)
    (g:X→(ℝ≥0×Ω)→C)(hc:∀ᵐz∂energyMeasure μ H,Continuous (fun x=>g x z))
    (hz:∀x z,z.1≤v→g x z=0)
    (K:X→Ω→ℝ)(hK:∀x,Measurable (K x))
    (hKc:∀ω,Continuous (fun x=>K x ω)){B:ℝ}(hB:0≤B)(hb:∀x ω,‖K x ω‖≤B)
    (hrep:∀x,∃input:Process (E:=C) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] g x ∧ J.integral input=ᵐ[μ] K x)
    {u:Ω→X}(hu:StronglyMeasurable[𝓕 v] u):
    ∃input:Process (E:=C) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>g (u z.2) z) ∧
      J.integral input=ᵐ[μ] fun ω=>K (u ω) ω:=by
  choose U hraw hrep using hrep
  have hpost(x:X):post 𝓕 μ H v (U x)=U x:=by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [PastItoInputs.post_ae 𝓕 μ H v (U x),hraw x] with z hp hg
    rw [hp,hg]
    by_cases ht:v<z.1
    · rw [if_pos ht]
    · rw [if_neg ht,hz x z (le_of_not_gt ht)]
  let s:=fun n:ℕ=>hu.approx n
  let input:=fun n:ℕ=>PastSimpleItoSelection.input 𝓕 μ H v U (s n)
  let F:=fun n:ℕ=>fun ω=>K ((s n) ω) ω
  let G:=fun ω=>K (u ω) ω
  have hm(n:ℕ):Measurable (F n):=
    PastParameterSectionExpectation.simple_eval_measurable (𝓕 v) (𝓕.le v) K hK (s n)
  have hgm:StronglyMeasurable G:=
    PastParameterDiagonal.stronglyMeasurable_diagonal (𝓕 v) (𝓕.le v) K hK hu hKc
  have hg:MemLp G 2 μ:=MemLp.of_bound hgm.aestronglyMeasurable B
    (Eventually.of_forall (fun ω=>hb (u ω) ω))
  have hi(n:ℕ):J.integral (input n)=ᵐ[μ] F n:=by
    have hs:=PastSimpleItoSelection.integral_ae 𝓕 μ H v U (s n) J hlocal
    have he:∀ᵐω∂μ,∀x∈@SimpleFunc.range Ω X (𝓕 v) (s n),J.integral (U x) ω=K x ω:=
      (Filter.eventually_all_finset _).mpr (fun x _=>hrep x)
    filter_upwards [hs,he] with ω hs he
    change J.integral (input n) ω=K ((s n) ω) ω
    rw [hs,hpost]
    exact he _ (@SimpleFunc.mem_range_self Ω X (𝓕 v) (s n) ω)
  have hr(n:ℕ):input n=ᵐ[energyMeasure μ H] (fun z=>g ((s n) z.2) z):=by
    have hs:=PastSimpleItoSelection.input_ae 𝓕 μ H v U (s n)
    have he:∀ᵐz∂energyMeasure μ H,∀x∈@SimpleFunc.range Ω X (𝓕 v) (s n),U x z=g x z:=
      (Filter.eventually_all_finset _).mpr (fun x _=>hraw x)
    filter_upwards [hs,he] with z hs he
    change input n z=g ((s n) z.2) z
    rw [hs]
    by_cases ht:v<z.1
    · rw [if_pos ht]
      exact he _ (@SimpleFunc.mem_range_self Ω X (𝓕 v) (s n) z.2)
    · rw [if_neg ht,hz _ z (le_of_not_gt ht)]
  have hl:Tendsto (fun n=>∫ω,‖F n ω-G ω‖^2 ∂μ) atTop (𝓝 0):=by
    have ht:=tendsto_integral_of_dominated_convergence (μ:=μ) (fun _=>(2*B)^2)
      (fun n=>((hm n).sub hgm.measurable).norm.pow_const 2 |>.aestronglyMeasurable)
      (integrable_const _)
      (fun n=>Eventually.of_forall (fun ω=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hn:=norm_sub_le (F n ω) (G ω)
        have hb':‖F n ω-G ω‖≤2*B:=hn.trans (by dsimp only [F,G];linarith [hb ((s n) ω) ω,hb (u ω) ω])
        exact pow_le_pow_left₀ (norm_nonneg _) hb' 2))
      (Eventually.of_forall (fun ω=>by
        have ht:=((((hKc ω).tendsto (u ω)).comp (hu.tendsto_approx ω)).sub_const (G ω)).norm.pow 2
        simpa only [F,G,s,Function.comp_def,Pi.sub_apply,sub_self,norm_zero,zero_pow (by norm_num:2≠0)] using ht))
    simpa only [Pi.sub_apply,integral_zero] using ht
  apply TerminalItoRawLimit.original_input 𝓕 μ H J input F G hg hi hl
    (fun n z=>g ((s n) z.2) z) (fun z=>g (u z.2) z) hr
  filter_upwards [hc] with z hzc
  exact hzc.continuousAt.tendsto.comp (hu.tendsto_approx z.2)

end SHE.PastParameterRawLimit
