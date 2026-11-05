module

public import SHE.PastParameterItoInput
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.PastParameterItoIdentity
open Set MeasureTheory PredictableL2 PastItoInputs Filter Topology PastParameterItoInput
open scoped NNReal ENNReal
open Classical
variable {Ω X C : Type*} [MeasurableSpace Ω]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable (v : ℝ≥0) (g : X→(ℝ≥0×Ω)→C)
variable (hg : @Measurable (X×(ℝ≥0×Ω)) C
  ((inferInstance : MeasurableSpace X).prod 𝓕.predictable) inferInstance (fun p => g p.1 p.2))
variable (b : Process (E:=ℝ) 𝓕 μ H) (hbound : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product 𝓕),∀ x,‖g x p‖≤‖b p‖) (e : X)

local notation "inp" => PastParameterItoInput.input 𝓕 μ H v g hg b hbound e

theorem post_input {u : Ω→X} (hu : Measurable[𝓕 v] u) :
    post 𝓕 μ H v (inp hu)=inp hu := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v (inp hu),input_ae 𝓕 μ H v g hg b hbound e hu] with p hp hi
  rw [hp,hi]
  by_cases ht : v<p.1 <;> simp [PastParameterItoInput.raw,ht]

/-- The constructed diagonal input at a finite past-simple parameter
is exactly the sum of original event-restricted inputs. -/
theorem simple_input (s : @SimpleFunc Ω (𝓕 v) X) :
    PastSimpleItoSelection.input 𝓕 μ H v (fun x=>inp (measurable_const (a:=x))) s=
      inp (@SimpleFunc.measurable Ω X (𝓕 v) inferInstance s) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  have he := (Filter.eventually_all_finset (@SimpleFunc.range Ω X (𝓕 v) s)).mpr
    (fun x _ => input_ae 𝓕 μ H v g hg b hbound e (measurable_const (a:=x)))
  filter_upwards [PastSimpleItoSelection.input_ae 𝓕 μ H v (fun x=>inp (measurable_const (a:=x))) s,
    input_ae 𝓕 μ H v g hg b hbound e (@SimpleFunc.measurable Ω X (𝓕 v) inferInstance s),he] with p hp hi hx
  rw [hp,hi]
  by_cases ht : v<p.1
  · rw [ite_eq_left ht,hx (s p.2) (@SimpleFunc.mem_range_self Ω X (𝓕 v) s p.2)]
    simp [PastParameterItoInput.raw,ht]
  · simp [PastParameterItoInput.raw,ht]

variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- A deterministic-parameter identity against the ORIGINAL integral
extends to an F_v-random parameter. The proof uses finite past-simple
selection, ordinary event pullout, dominated predictable-L² convergence,
and an almost-everywhere subsequence. This is not a new random-Itô input. -/
theorem diagonal_identity (hlocal : StandardTerminalPastLocality J)
    (hc : ∀ p,Continuous (fun x=>g x p))
    (K : X→Ω→ℝ) (hK : ∀ x,K x=ᵐ[μ] J.integral (inp (measurable_const (a:=x))))
    (hKcont : ∀ᵐ ω ∂μ,Continuous (fun x=>K x ω))
    {u : Ω→X} (hu : StronglyMeasurable[𝓕 v] u) :
    (fun ω=>K (u ω) ω)=ᵐ[μ] J.integral (inp hu.measurable) := by
  have ht := J.integral.continuous.continuousAt.tendsto.comp
    (PastParameterItoInput.approximation_tendsto 𝓕 μ H v g hg b hbound e hc hu)
  obtain ⟨ns,hns,hconv⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hsimple (n : ℕ) : J.integral (inp (@SimpleFunc.measurable Ω X (𝓕 v) inferInstance (hu.approx n)))=ᵐ[μ]
      fun ω=>K ((hu.approx n) ω) ω := by
    have hs := PastSimpleItoSelection.integral_ae 𝓕 μ H v
      (fun x=>inp (measurable_const (a:=x))) (hu.approx n) J hlocal
    have he := (Filter.eventually_all_finset (@SimpleFunc.range Ω X (𝓕 v) (hu.approx n))).mpr
      (fun x _=>hK x)
    rw [simple_input 𝓕 μ H v g hg b hbound e] at hs
    filter_upwards [hs,he] with ω hω hx
    rw [hω,post_input 𝓕 μ H v g hg b hbound e]
    exact (hx ((hu.approx n) ω) (@SimpleFunc.mem_range_self Ω X (𝓕 v) (hu.approx n) ω)).symm
  have he := ae_all_iff.mpr (fun n=>hsimple (ns n))
  filter_upwards [hconv,he,hKcont] with ω hω he hcK
  have hlim := (hcK.tendsto (u ω)).comp ((hu.tendsto_approx ω).comp hns.tendsto_atTop)
  exact tendsto_nhds_unique hlim (hω.congr' (Filter.Eventually.of_forall (fun n=>he n)))

end SHE.PastParameterItoIdentity
