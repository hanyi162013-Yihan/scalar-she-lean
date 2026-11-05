module

public import SHEStochastic.GlobalCanonicalFourierMildSolution
public import SHEStochastic.CanonicalMildFourierCharacteristics
public import SHEStochastic.NativeBoundedMartingaleVersion
public import SHEStochastic.CanonicalFourierDisintegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.GlobalCanonicalMildFourierCharacteristics
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {V ι : Type*} [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (H : ℝ≥0) (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
  (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn (filtration H) Q H
    (fun i ↦ coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0))
  (hH : 0<H)
  (hMild : GlobalBoundedFourierRecognition.HasClosedVersion (filtration H) Q H (state H) (state_predictable H)
    hG hβ hβ1 B hb hH (FiniteCylindricalIto.terminalIto
      (CanonicalNativeFourierRecognition.family H Q hBrown).toCoordinates e) (state H 0))

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

local notation "P" => CanonicalNativeFourierRecognition.family H Q hBrown
local notation "J" => FiniteCylindricalIto.terminalIto
  (FiniteScalarIto.Family.toCoordinates (CanonicalNativeFourierRecognition.family H Q hBrown)) e
local notation "input" => CanonicalNativeFourierInput.input hG hβ hβ1 B hb H Q

include hH hMild in
theorem represents (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
    CanonicalFourierFluctuation.value (ι := ι) H a n t =ᵐ[Q]
      (J).integral (StoppedItoInputs.stop (filtration H) Q H t (input a n)) := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  have hzero : clock H 0 = StoppedPathPasting.origin H := by
    apply Subtype.ext
    change min ((0 : ℝ≥0) : ℝ) (H : ℝ) = 0
    rw [NNReal.coe_zero]
    exact min_eq_left H.property
  have hh := GlobalBoundedFourierRecognition.fourier_of_closed (filtration H) Q H (state H)
    (state_predictable H) hG hβ hβ1 B hb hH J (state H 0) hMild
    (min t H) (min_le_right _ _) a n
  rw [CanonicalProcessTimeRegularity.fourier_clip H a n t]
  rw [← NativeBoundedMartingaleVersion.stop_cap (input a n) t]
  convert hh using 1
  · funext x
    simp only [CanonicalFourierFluctuation.value, state]
    rw [hzero]
    simp only [clock, NNReal.coe_min, min_assoc, min_self]
  · simp only [NNReal.coe_min, CanonicalNativeFourierInput.input]

include hH hMild in
/-- Full-horizon characteristics reuse the common native stochastic
calculus proof after identifying the original retained-driver integral. -/
theorem holds : CanonicalMildFourierCharacteristics.Holds H Q hG hβ hβ1 B hb e :=
  CanonicalMildFourierCharacteristics.holds_of_representation H Q hG hβ hβ1 B hb e hBrown
    (represents H Q hG hβ hβ1 B hb e hBrown hH hMild)

end SHEStochastic.GlobalCanonicalMildFourierCharacteristics
