module

public import SHEStochastic.CanonicalNativeFourierInput
public import SHEStochastic.NativeCharacteristicRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.CanonicalNativeFourierRecognition
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation
open SHE.FiniteHaar AddCircle CanonicalStateDriverFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0)
  (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]

/-- The canonical driver family uses the full state-and-driver past. -/
def family (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn (filtration H) Q H
    (fun i ↦ coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0)) :
    FiniteScalarIto.Family (filtration (E := RealL2) H) Q H ι :=
  ⟨⟨coordinate H, coordinate_adapted H, hBrown⟩, coordinate_continuous H⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

/-- Native Fourier equation, kept as one interface for weak limits and
the later conversion to heat observations. -/
def Solves
    (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn (filtration H) Q H
      (fun i ↦ coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0))
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) : Prop :=
  ∀ t, t ≤ H → CanonicalFourierFluctuation.value (ι := ι) H a n t =ᵐ[Q]
    (FiniteCylindricalIto.terminalIto (family H Q hBrown).toCoordinates e).integral
      (StoppedItoInputs.stop (filtration H) Q H t
        (CanonicalNativeFourierInput.input hG hβ hβ1 B hb H Q a n))

/-- Square and mixed canonical characteristics identify the actual
native Fourier integral with the retained Brownian driver. -/
theorem equation
    (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn (filtration H) Q H
      (fun i ↦ coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0))
    (a : ℂ →L[ℝ] ℝ) (n : ℤ)
    (hM : Martingale (CanonicalFourierFluctuation.value (ι := ι) H a n) (filtration H) Q)
    (hM2 : ∀ t, t ≤ H → MemLp (CanonicalFourierFluctuation.value (ι := ι) H a n t) 2 Q)
    (hSquare : Martingale (fun t x ↦ (CanonicalFourierFluctuation.value (ι := ι) H a n t x)^2-
      NativeFourierSquareTests.compensator hG hβ hβ1 B hb a n H t x) (filtration H) Q)
    (hMixed : ∀ i, Martingale (fun t x ↦ CanonicalFourierFluctuation.value (ι := ι) H a n t x *
      coordinate H i t x-NativeFourierMixedTests.compensator hG hβ hβ1 B hb a n (e i) H t x)
      (filtration H) Q) :
    Solves H Q hG hβ hβ1 B hb e hBrown a n := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  let P := family H Q hBrown
  let r := CanonicalNativeFourierInput.input hG hβ hβ1 B hb H Q a n
  let M := CanonicalFourierFluctuation.value (ι := ι) H a n
  have hclip (i : ι) (t : ℝ≥0) : P.W i t = P.W i (min t H) := by
    funext x
    simp only [P, family, coordinate, clock, NNReal.coe_min, min_assoc, min_self]
  have hS : Martingale (fun t x ↦ M t x^2-PredictableBracket.energy r t x) (filtration H) Q := by
    apply hSquare.congr
    · intro t
      exact ((hM.stronglyAdapted t).pow 2).sub (PredictableBracket.measurable r t).stronglyMeasurable
    · intro t
      filter_upwards [CanonicalNativeFourierInput.energy hG hβ hβ1 B hb H Q a n t] with x hx
      change M t x^2-_ = M t x^2-_
      rw [hx]
  have hC (i : ι) : Martingale (fun t x ↦ M t x*P.W i t x-
      NativeCrossCompensator.value r (RotatedCylindricalCoordinates.constant (filtration H) Q H (e i)) t x)
      (filtration H) Q := by
    apply (hMixed i).congr
    · intro t
      let v := RotatedCylindricalCoordinates.constant (filtration H) Q H (e i)
      have ha : StronglyMeasurable[(filtration H) t] (NativeCrossCompensator.value r v t) :=
        (((PredictableBracket.measurable r t).stronglyMeasurable.add
          (PredictableBracket.measurable v t).stronglyMeasurable).sub
            (PredictableBracket.measurable (r-v) t).stronglyMeasurable).div stronglyMeasurable_const
      exact ((hM.stronglyAdapted t).mul (P.adapted i t).stronglyMeasurable).sub ha
    · intro t
      filter_upwards [CanonicalNativeFourierInput.mixed hG hβ hβ1 B hb H Q a n (e i) t] with x hx
      change M t x*coordinate H i t x-_ = M t x*coordinate H i t x-_
      rw [hx]
  have hz : M 0 =ᵐ[Q] fun _ ↦ (0 : ℝ) := Filter.Eventually.of_forall fun x ↦ by
    simp [M, CanonicalFourierFluctuation.value, clock, StoppedPathPasting.origin]
  exact NativeCharacteristicRecognition.process P e r M hM hM2
    (NativeHorizonCharacteristics.coordinates P e hclip) hz hS hC

end SHEStochastic.CanonicalNativeFourierRecognition
