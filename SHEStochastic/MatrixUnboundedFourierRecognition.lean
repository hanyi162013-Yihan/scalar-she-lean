module

public import SHEStochastic.MatrixUnboundedCanonicalInput
public import SHEStochastic.MatrixCanonicalFourierRecognition
public import SHEStochastic.NativeCharacteristicRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixUnboundedFourierRecognition
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
variable (H : ℝ≥0)
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n)) (ι := Fin n×FiniteHaar.HaarNode) H))
    [IsProbabilityMeasure Q]

variable (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hEnergy : Integrable (fun x => ‖x.1‖^2) Q)
    (hBrown : ∀ m (j : Fin m → Fin n×FiniteHaar.HaarNode),FiniteBrownianLawOn
      (filtration H) Q H (fun i => CanonicalStateDriverFiltration.coordinate H (j i))
      (fun i k => if j i=j k then 1 else 0))
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ)
local notation "M" => CanonicalLinearFluctuation.value (ι := Fin n×FiniteHaar.HaarNode) H
  (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2)

def Solves : Prop := ∀ t,t ≤ H → M t =ᵐ[Q]
  (FiniteCylindricalIto.terminalIto (MatrixCanonicalFourierRecognition.family H Q hBrown).toCoordinates MatrixPredictableHaarRotation.basis).integral
    (StoppedItoInputs.stop (filtration H) Q H t (MatrixUnboundedCanonicalInput.input G hG hβ hβ1 H Q hEnergy i a freq))

/-- The limiting square and driver cross characteristics identify the
actual matrix Fourier stochastic integral against the retained Brownian family. -/
theorem equation (hM : Martingale M (filtration H) Q)
    (hM2 : ∀ t,t ≤ H → MemLp (M t) 2 Q)
    (hSquare : Martingale (fun t x => M t x^2-MatrixUnboundedFourierCompensator.square G hG hβ hβ1 H i a freq t x)
      (filtration H) Q)
    (hMixed : ∀ k,Martingale (fun t x => M t x*CanonicalStateDriverFiltration.coordinate H k t x-
      MatrixUnboundedFourierCompensator.mixed G hG hβ hβ1 H i a freq k t x) (filtration H) Q) :
    Solves H Q G hG hβ hβ1 hEnergy hBrown i a freq := by
  let P := MatrixCanonicalFourierRecognition.family H Q hBrown
  let r := MatrixUnboundedCanonicalInput.input G hG hβ hβ1 H Q hEnergy i a freq
  have hclip (k : Fin n×FiniteHaar.HaarNode) (t : ℝ≥0) : P.W k t=P.W k (min t H) := by
    funext x
    simp only [P,MatrixCanonicalFourierRecognition.family,CanonicalStateDriverFiltration.coordinate,clock,NNReal.coe_min,min_assoc,min_self]
  have hS : Martingale (fun t x => M t x^2-PredictableBracket.energy r t x) (filtration H) Q := by
    apply hSquare.congr
    · intro t
      exact ((hM.stronglyAdapted t).pow 2).sub (PredictableBracket.measurable r t).stronglyMeasurable
    · intro t
      filter_upwards [MatrixUnboundedCanonicalInput.energy G hG hβ hβ1 H Q hEnergy i a freq t] with x hx
      change M t x^2-_=M t x^2-_
      rw [hx]
  have hC (k : Fin n×FiniteHaar.HaarNode) : Martingale (fun t x => M t x*P.W k t x-
      NativeCrossCompensator.value r (RotatedCylindricalCoordinates.constant (filtration H) Q H
        (MatrixPredictableHaarRotation.basis k)) t x) (filtration H) Q := by
    apply (hMixed k).congr
    · intro t
      let v := RotatedCylindricalCoordinates.constant (filtration H) Q H (MatrixPredictableHaarRotation.basis k)
      have ha : StronglyMeasurable[(filtration H) t] (NativeCrossCompensator.value r v t) :=
        (((PredictableBracket.measurable r t).stronglyMeasurable.add
          (PredictableBracket.measurable v t).stronglyMeasurable).sub
            (PredictableBracket.measurable (r-v) t).stronglyMeasurable).div stronglyMeasurable_const
      exact ((hM.stronglyAdapted t).mul (P.adapted k t).stronglyMeasurable).sub ha
    · intro t
      filter_upwards [MatrixUnboundedCanonicalInput.mixed G hG hβ hβ1 H Q hEnergy i a freq k t] with x hx
      change M t x*CanonicalStateDriverFiltration.coordinate H k t x-_=M t x*CanonicalStateDriverFiltration.coordinate H k t x-_
      rw [hx]
  have hz : M 0 =ᵐ[Q] fun _ => (0 : ℝ) := Filter.Eventually.of_forall (CanonicalLinearFluctuation.zero H
    (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2))
  exact NativeCharacteristicRecognition.process P MatrixPredictableHaarRotation.basis r M hM hM2
    (NativeHorizonCharacteristics.coordinates P MatrixPredictableHaarRotation.basis hclip) hz hS hC

end SHEStochastic.MatrixUnboundedFourierRecognition
