module

public import SHE.PastSimpleItoSelection
public import SHE.PredictableDominatedLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.PastParameterItoInput
open Set MeasureTheory PredictableL2 PastItoInputs Filter Topology
open scoped NNReal ENNReal
variable {Ω X C : Type*} [MeasurableSpace Ω]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
variable (v : ℝ≥0) (g : X→(ℝ≥0×Ω)→C)
variable (hg : @Measurable (X×(ℝ≥0×Ω)) C
  ((inferInstance : MeasurableSpace X).prod 𝓕.predictable) inferInstance (fun p => g p.1 p.2))
variable (b : Process (E:=ℝ) 𝓕 μ H) (hbound : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product 𝓕),∀ x,‖g x p‖≤‖b p‖)
variable (e : X)

/-- A past-known random parameter is used only strictly after its
availability time. The process is zero before that time. -/
def raw (u : Ω→X) (p : ℝ≥0×Ω) : C := if v<p.1 then g (u p.2) p else 0

include hg e in
theorem raw_predictable {u : Ω→X} (hu : Measurable[𝓕 v] u) :
    StronglyMeasurable[𝓕.predictable] (raw v g u) := by
  have hm := hg.comp ((PredictablePastParameter.held_measurable 𝓕 v u hu e).prodMk measurable_id)
  have he : raw v g u=(Ioi v×ˢ (univ:Set Ω)).indicator
      (fun p=>g (PredictablePastParameter.held v u e p) p) := by
    funext p
    by_cases hp : v<p.1 <;> simp [raw,PredictablePastParameter.held,hp]
  rw [he]
  exact (hm.indicator (measurableSet_predictable_Ioi_prod MeasurableSet.univ)).stronglyMeasurable

include hg hbound e in
theorem raw_memLp {u : Ω→X} (hu : Measurable[𝓕 v] u) :
    @MemLp (ℝ≥0×Ω) C 𝓕.predictable _ _ (raw v g u) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
  apply (Lp.memLp b).of_le ((raw_predictable 𝓕 v g hg e hu).aestronglyMeasurable)
  filter_upwards [hbound] with p hpbound
  by_cases hp : v<p.1
  · simpa only [raw,ite_eq_left hp] using hpbound (u p.2)
  · simp only [raw,ite_eq_right hp,norm_zero]
    exact norm_nonneg _
/-
    by_cases hp : v<p.1
    · simpa only [raw,ite_eq_left hp] using hbnd (u p.2)
    · simp only [raw,ite_eq_right hp,norm_zero]
      exact norm_nonneg _)
-/

def input {u : Ω→X} (hu : Measurable[𝓕 v] u) : Process (E:=C) 𝓕 μ H :=
  (raw_memLp 𝓕 μ H v g hg b hbound e hu).toLp (raw v g u)

theorem input_ae {u : Ω→X} (hu : Measurable[𝓕 v] u) :
    input 𝓕 μ H v g hg b hbound e hu =ᵐ[energyMeasure μ H] raw v g u :=
  ae_eq_of_ae_eq_trim (raw_memLp 𝓕 μ H v g hg b hbound e hu).coeFn_toLp

include hg hbound in
theorem input_bound {u : Ω→X} (hu : Measurable[𝓕 v] u) :
    ∀ᵐ p ∂energyMeasure μ H,‖input 𝓕 μ H v g hg b hbound e hu p‖≤‖b p‖ := by
  filter_upwards [input_ae 𝓕 μ H v g hg b hbound e hu,ae_of_ae_trim (predictable_le_product 𝓕) hbound] with p hp hbnd
  rw [hp]
  by_cases ht : v<p.1
  · simpa only [raw,ite_eq_left ht] using hbnd (u p.2)
  · simp [raw,ht]

/-- Finite past-simple approximants converge in the ORIGINAL
predictable L² space to the actual diagonal input. -/
theorem approximation_tendsto (hc : ∀ p,Continuous (fun x=>g x p))
    {u : Ω→X} (hu : StronglyMeasurable[𝓕 v] u) :
    Tendsto (fun n=>input 𝓕 μ H v g hg b hbound e (@SimpleFunc.measurable Ω X (𝓕 v) inferInstance (hu.approx n)))
      atTop (𝓝 (input 𝓕 μ H v g hg b hbound e hu.measurable)) := by
  let U := fun n=>input 𝓕 μ H v g hg b hbound e (@SimpleFunc.measurable Ω X (𝓕 v) inferInstance (hu.approx n))
  let V := input 𝓕 μ H v g hg b hbound e hu.measurable
  apply PredictableDominatedLimit.tendsto 𝓕 μ H U V (fun p=>‖b p‖)
    (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp b)).norm.integrable_sq
    (fun n=>input_bound 𝓕 μ H v g hg b hbound e (@SimpleFunc.measurable Ω X (𝓕 v) inferInstance (hu.approx n)))
    (input_bound 𝓕 μ H v g hg b hbound e hu.measurable)
  have he := ae_all_iff.mpr (fun n=>input_ae 𝓕 μ H v g hg b hbound e (@SimpleFunc.measurable Ω X (𝓕 v) inferInstance (hu.approx n)))
  filter_upwards [he,input_ae 𝓕 μ H v g hg b hbound e hu.measurable] with p hp hv
  change Tendsto (fun n=>U n p) atTop (𝓝 (V p))
  change V p=raw v g u p at hv
  rw [hv]
  have heq : (fun n=>U n p)=fun n=>raw v g (hu.approx n) p := funext (fun n=>hp n)
  rw [heq]
  by_cases ht : v<p.1
  · simp only [raw,ite_eq_left ht]
    exact (hc p).continuousAt.tendsto.comp (hu.tendsto_approx p.2)
  · simp only [raw,ite_eq_right ht]
    exact tendsto_const_nhds

end SHE.PastParameterItoInput
