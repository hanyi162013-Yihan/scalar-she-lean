module

public import SHE.PastParameterConditional
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PastParameterSectionExpectation
open Set MeasureTheory Filter Topology
open Classical
variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable (m : MeasurableSpace Ω) (hm : m≤mΩ) (μ : @Measure Ω mΩ)
variable (K : X→Ω→ℝ)
variable (hK : ∀ x,@Measurable Ω ℝ mΩ inferInstance (K x))
variable (b : Ω→ℝ) (hb : Integrable b μ) (hbound : ∀ x ω,‖K x ω‖≤b ω)
variable (hzero : ∀ x A,MeasurableSet[m] A → (∫ ω in A,K x ω ∂μ)=0)

include hm hK in
theorem simple_eval_measurable (s : @SimpleFunc Ω m X) :
    @Measurable Ω ℝ mΩ inferInstance (fun ω => K (s ω) ω) := by
  have he : (fun ω => K (s ω) ω)=fun ω => ∑ x∈s.range,({ω | s ω=x}.indicator (K x)) ω := by
    funext ω
    symm
    calc
      (∑ x∈s.range,({ω | s ω=x}.indicator (K x)) ω)=({ω | s ω=s ω}.indicator (K (s ω))) ω := by
        apply Finset.sum_eq_single (s ω)
        · intro x hx hne
          have hneq : s ω≠x := Ne.symm hne
          simp only [Set.indicator,mem_setOf_eq,hneq,ite_false]
        · exact fun hn => (hn (s.mem_range_self ω)).elim
      _ = K (s ω) ω := by simp
  rw [he]
  exact Finset.measurable_fun_sum _ (fun x _ => (hK x).indicator (hm _ (s.measurableSet_fiber x)))

include hm hK hb hbound hzero in
theorem integral_simple_eq_zero (s : @SimpleFunc Ω m X) :
    (∫ ω,K (s ω) ω ∂μ)=0 := by
  have hi (x : X) : Integrable (K x) μ :=
    hb.mono' (hK x).aestronglyMeasurable
      (Eventually.of_forall (hbound x))
  have hf (x : X) : MeasurableSet[mΩ] {ω | s ω=x} := hm _ (s.measurableSet_fiber x)
  have hI (x : X) : Integrable ({ω | s ω=x}.indicator (K x)) μ := (hi x).indicator (hf x)
  have he : (fun ω => K (s ω) ω)=fun ω => ∑ x∈s.range,({ω | s ω=x}.indicator (K x)) ω := by
    funext ω
    symm
    calc
      (∑ x∈s.range,({ω | s ω=x}.indicator (K x)) ω)=({ω | s ω=s ω}.indicator (K (s ω))) ω := by
        apply Finset.sum_eq_single (s ω)
        · intro x hx hne
          have hneq : s ω≠x := Ne.symm hne
          simp only [Set.indicator,mem_setOf_eq,hneq,ite_false]
        · exact fun hn => (hn (s.mem_range_self ω)).elim
      _ = K (s ω) ω := by simp
  rw [he,integral_finset_sum _ (fun x _ => hI x)]
  apply Finset.sum_eq_zero
  intro x hx
  rw [integral_indicator (hf x)]
  exact hzero x _ (s.measurableSet_fiber x)

include hm hK hb hbound hzero in
/-- A genuine deterministic substitution theorem for F_v-random
parameters. It is proved using finite simple approximants and dominated
convergence; no random-reference Itô formula is assumed. -/
theorem integral_random_eq_zero {u : Ω→X} (hu : StronglyMeasurable[m] u)
    (hc : ∀ ω,Continuous (fun x => K x ω)) :
    Integrable (fun ω => K (u ω) ω) μ ∧ (∫ ω,K (u ω) ω ∂μ)=0 := by
  have hum : @Measurable Ω X mΩ inferInstance u := hu.measurable.mono hm le_rfl
  have hmn (n : ℕ) : @Measurable Ω ℝ mΩ inferInstance (fun ω => K ((hu.approx n) ω) ω) :=
    simple_eval_measurable (mΩ := mΩ) m hm K hK (hu.approx n)
  have hmd : @StronglyMeasurable Ω ℝ _ mΩ (fun ω => K (u ω) ω) := by
    apply stronglyMeasurable_of_tendsto atTop (fun n => (hmn n).stronglyMeasurable)
    exact tendsto_pi_nhds.mpr (fun ω => ((hc ω).tendsto (u ω)).comp (hu.tendsto_approx ω))
  have him : Integrable (fun ω => K (u ω) ω) μ :=
    hb.mono' hmd.aestronglyMeasurable (Eventually.of_forall (fun ω => hbound _ ω))
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ) b
    (Eventually.of_forall (fun n => (hmn n).aestronglyMeasurable))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun ω => hbound ((hu.approx n) ω) ω))) hb
    (Eventually.of_forall (fun ω => ((hc ω).tendsto (u ω)).comp (hu.tendsto_approx ω)))
  have hz (n : ℕ) : (∫ ω,K ((hu.approx n) ω) ω ∂μ)=0 :=
    integral_simple_eq_zero (mΩ := mΩ) m hm μ K hK b hb hbound hzero (hu.approx n)
  have ht0 : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 (∫ ω,K (u ω) ω ∂μ)) :=
    ht.congr' (Eventually.of_forall hz)
  exact ⟨him,tendsto_nhds_unique ht0 tendsto_const_nhds⟩

end SHE.PastParameterSectionExpectation
