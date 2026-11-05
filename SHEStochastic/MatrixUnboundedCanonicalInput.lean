module

public import SHEStochastic.MatrixUnboundedNativeCompensator
public import SHEStochastic.MatrixUnboundedFourierCompensator
public import SHEStochastic.NativeHorizonCharacteristics

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixUnboundedCanonicalInput
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates CanonicalStateDriverFiltration
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1) (H : ℝ≥0)
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n)) (ι := Fin n×FiniteHaar.HaarNode) H))
    [IsProbabilityMeasure Q]
    (hEnergy : Integrable (fun x => ‖x.1‖^2) Q)
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ)

include hEnergy in
/-- Finite full path energy supplies the predictable input energy. -/
theorem state_energy : Integrable
    (fun p : ℝ≥0×CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×FiniteHaar.HaarNode) H => ‖state H p.1 p.2‖^2) (energyMeasure Q H) := by
  have hi := hEnergy.comp_snd (PredictableL2.timeMeasure H)
  apply hi.mono'
  · exact (((state_predictable (E := Physical (d := Fin n))
      (ι := Fin n×FiniteHaar.HaarNode) H).mono (predictable_le_product (filtration H))).norm.pow 2).aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm p.2.1 (clock H p.1)) 2

def input : Process (E := Input (d := Fin n)) (filtration H) Q H :=
  MatrixUnboundedFourierInput.input (filtration H) Q H G hG hβ hβ1
    (fun p => state H p.1 p.2) (state_predictable H) (state_energy H Q hEnergy) i a freq

/-- The path-law square compensator is the actual canonical native
input energy, including after the capped horizon. -/
theorem energy (t : ℝ≥0) :
    (fun x => MatrixUnboundedFourierCompensator.square G hG hβ hβ1 H i a freq t x) =ᵐ[Q]
      PredictableBracket.energy (input G hG hβ hβ1 H Q hEnergy i a freq) t := by
  filter_upwards [MatrixUnboundedNativeCompensator.energy_ae (filtration H) Q H G hG hβ hβ1
    (fun p => state H p.1 p.2) (state_predictable H) (state_energy H Q hEnergy) i a freq,
    NativeHorizonCharacteristics.energy_clip (input G hG hβ hβ1 H Q hEnergy i a freq) t] with x hx hc
  change ContinuousCanonicalCompensator.value H (2*(freq : ℝ)^2) _
    (MatrixUnboundedNativeCompensator.diagonal G hG hβ hβ1 i a freq) t x=_
  rw [ContinuousCanonicalCompensator.canonical_value,← hx (min t H) (min_le_right _ _)]
  exact hc

/-- The same equality for every retained canonical Brownian coordinate. -/
theorem mixed (k : Fin n×FiniteHaar.HaarNode) (t : ℝ≥0) :
    (fun x => MatrixUnboundedFourierCompensator.mixed G hG hβ hβ1 H i a freq k t x) =ᵐ[Q]
      NativeCrossCompensator.value (input G hG hβ hβ1 H Q hEnergy i a freq)
        (RotatedCylindricalCoordinates.constant (filtration H) Q H (MatrixPredictableHaarRotation.basis k)) t := by
  filter_upwards [MatrixUnboundedNativeCompensator.mixed_ae (filtration H) Q H G hG hβ hβ1
    (fun p => state H p.1 p.2) (state_predictable H) (state_energy H Q hEnergy) i a freq (MatrixPredictableHaarRotation.basis k),
    NativeHorizonCharacteristics.cross_clip (input G hG hβ hβ1 H Q hEnergy i a freq)
      (RotatedCylindricalCoordinates.constant (filtration H) Q H (MatrixPredictableHaarRotation.basis k)) t] with x hx hc
  change ContinuousCanonicalCompensator.value H ((freq : ℝ)^2) _
    (MatrixUnboundedNativeCompensator.mixed G hG hβ hβ1 i a freq
      (MatrixPredictableHaarRotation.basis k)) t x=_
  rw [ContinuousCanonicalCompensator.canonical_value,← hx (min t H) (min_le_right _ _)]
  exact hc

end SHEStochastic.MatrixUnboundedCanonicalInput
