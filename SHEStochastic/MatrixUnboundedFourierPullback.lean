module

public import SHEStochastic.MatrixFourierPullback
public import SHEStochastic.MatrixUnboundedFourierInput
public import SHEStochastic.CylindricalProcessPullback

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixUnboundedFourierPullback
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates MatrixFourierPullback
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω Ξ : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 mΩ} {D : Filtration ℝ≥0 mΞ}
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}
    (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ) (hfil : ∀ t,@Measurable Ξ Ω (D t) (F t) π)
    (G : EuclideanSpace ℝ d → Matrix d d ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)

    (hEnergy : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H))

/-- The same unbounded Fourier equation on any predictable probability space. -/
def Equation (P : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode)) (Z : Ω → Physical (d := d)) : Prop :=
  ∀ (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0),t≤H →
    (fun ω => Real.exp ((t : ℝ)*(n : ℝ)^2)*coordinate i a n (U (t,ω))) =ᵐ[μ]
      fun ω => coordinate i a n (Z ω)+
        (FiniteCylindricalIto.terminalIto P.toCoordinates MatrixPredictableHaarRotation.basis).integral
          (StoppedItoInputs.stop F μ H t
            (MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 U hU hEnergy i a n)) ω

include hπ hEnergy in
/-- Input energy is preserved by the existing filtered pullback. -/
theorem energy : Integrable (fun p => ‖state π U p‖^2) (energyMeasure ν H) :=
  ((MeasurePreserving.id (PredictableL2.timeMeasure H)).prod hπ).integrable_comp_of_integrable hEnergy

include hπ in
theorem input_ae (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    MatrixUnboundedFourierInput.input D ν H G hG hβ hβ1 (state π U) (predictable π hfil U hU) (energy π hπ U hEnergy) i a n =ᵐ[energyMeasure ν H]
      fun p => MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 U hU hEnergy i a n (FilteredPullback.timeMap π p) := by
  have hp : MeasurePreserving (FilteredPullback.timeMap π) (energyMeasure ν H) (energyMeasure μ H) :=
    (MeasurePreserving.id (PredictableL2.timeMeasure H)).prod hπ
  filter_upwards [MatrixUnboundedFourierInput.input_ae D ν H G hG hβ hβ1 (state π U) (predictable π hfil U hU) (energy π hπ U hEnergy) i a n,
    hp.quasiMeasurePreserving.ae (MatrixUnboundedFourierInput.input_ae F μ H G hG hβ hβ1 U hU hEnergy i a n)] with p hn ho
  rw [hn,ho]
  rfl

include hπ in
/-- Matrix native Fourier equations survive the existing completed,
measure-preserving filtered pullback. -/
theorem equation (P : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode))
    (Q : FiniteScalarIto.Family D ν H (d×FiniteHaar.HaarNode))
    (hDriver : ∀ i t z,Q.W i t z=P.W i t (π z)) (Z : Ω → Physical (d := d))
    (hEquation : Equation (F := F) (μ := μ) (H := H) G hG hβ hβ1 U hU hEnergy P Z) :
    Equation (F := D) (μ := ν) (H := H) G hG hβ hβ1 (state π U)
      (predictable π hfil U hU) (energy π hπ U hEnergy) Q (Z ∘ π) := by
  intro i a n T hT
  let u := MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 U hU hEnergy i a n
  let v := MatrixUnboundedFourierInput.input D ν H G hG hβ hβ1 (state π U) (predictable π hfil U hU) (energy π hπ U hEnergy) i a n
  have hp : MeasurePreserving (FilteredPullback.timeMap π) (energyMeasure ν H) (energyMeasure μ H) :=
    (MeasurePreserving.id (PredictableL2.timeMeasure H)).prod hπ
  have hr : StoppedItoInputs.stop D ν H T v =ᵐ[energyMeasure ν H]
      fun p => (LinearIsometry.id : Input (d := d) →ₗᵢ[ℝ] _)
        (StoppedItoInputs.stop F μ H T u (FilteredPullback.timeMap π p)) := by
    filter_upwards [StoppedItoInputs.stop_ae D ν H T v,
      hp.quasiMeasurePreserving.ae (StoppedItoInputs.stop_ae F μ H T u),
      input_ae π hπ hfil G hG hβ hβ1 U hU hEnergy i a n] with p hn ho hi
    rw [hn,ho]
    change (StoppedItoInputs.before T).indicator v p=(StoppedItoInputs.before T).indicator u (FilteredPullback.timeMap π p)
    by_cases ht : (p.1 : ℝ)<T
    · simpa only [StoppedItoInputs.before,FilteredPullback.timeMap,Set.indicator_apply,Set.mem_setOf_eq,ht,ite_true] using hi
    · simp only [StoppedItoInputs.before,FilteredPullback.timeMap,Set.indicator_apply,Set.mem_setOf_eq,ht,ite_false]
  have hj := CylindricalPullback.process_naturality π hπ hfil P Q
    MatrixPredictableHaarRotation.basis MatrixPredictableHaarRotation.basis LinearIsometry.id id
    (fun _ => rfl) hDriver (StoppedItoInputs.stop F μ H T u) (StoppedItoInputs.stop D ν H T v) hr
  filter_upwards [hπ.quasiMeasurePreserving.ae (hEquation i a n T hT),hj] with z he hj
  exact he.trans (congrArg (fun r : ℝ => coordinate i a n (Z (π z))+r) hj.symm)

end SHEStochastic.MatrixUnboundedFourierPullback
