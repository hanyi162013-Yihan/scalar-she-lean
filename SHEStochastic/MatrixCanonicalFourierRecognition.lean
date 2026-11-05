module

public import SHEStochastic.MatrixCanonicalFourierInput
public import SHEStochastic.NativeCharacteristicRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixCanonicalFourierRecognition
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates CanonicalStateDriverFiltration
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (H : ℝ≥0)
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H))
    [IsProbabilityMeasure Q]

/-- The actual Brownian coordinates in the full canonical filtration. -/
def family (hBrown : ∀ m (j : Fin m → d×FiniteHaar.HaarNode),FiniteBrownianLawOn
    (filtration H) Q H (fun i => CanonicalStateDriverFiltration.coordinate H (j i))
    (fun i k => if j i=j k then 1 else 0)) :
    FiniteScalarIto.Family (filtration H) Q H (d×FiniteHaar.HaarNode) :=
  ⟨⟨CanonicalStateDriverFiltration.coordinate H,coordinate_adapted H,hBrown⟩,coordinate_continuous H⟩

variable (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hBrown : ∀ m (j : Fin m → d×FiniteHaar.HaarNode),FiniteBrownianLawOn
      (filtration H) Q H (fun i => CanonicalStateDriverFiltration.coordinate H (j i))
      (fun i k => if j i=j k then 1 else 0))
    (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
local notation "M" => CanonicalLinearFluctuation.value (ι := d×FiniteHaar.HaarNode) H
  (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2)

def Solves : Prop := ∀ t,t ≤ H → M t =ᵐ[Q]
  (FiniteCylindricalIto.terminalIto (family H Q hBrown).toCoordinates MatrixPredictableHaarRotation.basis).integral
    (StoppedItoInputs.stop (filtration H) Q H t (MatrixCanonicalFourierInput.input G hG hβ hβ1 H Q i a n))

/-- The limiting square and driver cross characteristics identify the
actual matrix Fourier stochastic integral against the retained Brownian family. -/
theorem equation (hM : Martingale M (filtration H) Q)
    (hM2 : ∀ t,t ≤ H → MemLp (M t) 2 Q)
    (hSquare : Martingale (fun t x => M t x^2-MatrixFourierSquareTests.compensator H G hG hβ hβ1 i a n t x)
      (filtration H) Q)
    (hMixed : ∀ k,Martingale (fun t x => M t x*CanonicalStateDriverFiltration.coordinate H k t x-
      MatrixFourierMixedTests.compensator H G hG hβ hβ1 i a n k t x) (filtration H) Q) :
    Solves H Q G hG hβ hβ1 hBrown i a n := by
  let P := family H Q hBrown
  let r := MatrixCanonicalFourierInput.input G hG hβ hβ1 H Q i a n
  have hclip (k : d×FiniteHaar.HaarNode) (t : ℝ≥0) : P.W k t=P.W k (min t H) := by
    funext x
    simp only [P,family,CanonicalStateDriverFiltration.coordinate,clock,NNReal.coe_min,min_assoc,min_self]
  have hS : Martingale (fun t x => M t x^2-PredictableBracket.energy r t x) (filtration H) Q := by
    apply hSquare.congr
    · intro t
      exact ((hM.stronglyAdapted t).pow 2).sub (PredictableBracket.measurable r t).stronglyMeasurable
    · intro t
      filter_upwards [MatrixCanonicalFourierInput.energy G hG hβ hβ1 H Q i a n t] with x hx
      change M t x^2-_=M t x^2-_
      rw [hx]
  have hC (k : d×FiniteHaar.HaarNode) : Martingale (fun t x => M t x*P.W k t x-
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
      filter_upwards [MatrixCanonicalFourierInput.mixed G hG hβ hβ1 H Q i a n k t] with x hx
      change M t x*CanonicalStateDriverFiltration.coordinate H k t x-_=M t x*CanonicalStateDriverFiltration.coordinate H k t x-_
      rw [hx]
  have hz : M 0 =ᵐ[Q] fun _ => (0 : ℝ) := Filter.Eventually.of_forall (CanonicalLinearFluctuation.zero H
    (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2))
  exact NativeCharacteristicRecognition.process P MatrixPredictableHaarRotation.basis r M hM hM2
    (NativeHorizonCharacteristics.coordinates P MatrixPredictableHaarRotation.basis hclip) hz hS hC

end SHEStochastic.MatrixCanonicalFourierRecognition
