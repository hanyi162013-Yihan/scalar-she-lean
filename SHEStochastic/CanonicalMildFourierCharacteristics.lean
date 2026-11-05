module

public import SHEStochastic.CanonicalFourierMildSolution
public import SHEStochastic.NativeBoundedMartingaleVersion
public import SHEStochastic.CanonicalFourierDisintegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.CanonicalMildFourierCharacteristics
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
  (hH1 : H ≤ 1)
  (hMild : BoundedFourierMildRecognition.HasClosedVersion (filtration H) Q H (state H) (state_predictable H)
    hG hβ hβ1 B hb (FiniteCylindricalIto.terminalIto
      (CanonicalNativeFourierRecognition.family H Q hBrown).toCoordinates e) (state H 0))

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

local notation "P" => CanonicalNativeFourierRecognition.family H Q hBrown
local notation "J" => FiniteCylindricalIto.terminalIto
  (FiniteScalarIto.Family.toCoordinates (CanonicalNativeFourierRecognition.family H Q hBrown)) e
local notation "input" => CanonicalNativeFourierInput.input hG hβ hβ1 B hb H Q

include hH1 hMild in
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
  have hh := BoundedFourierMildRecognition.fourier_of_closed (filtration H) Q H (state H)
    (state_predictable H) hG hβ hβ1 B hb J (state H 0) hMild
    (min t H) (min_le_right _ _) (by exact_mod_cast (min_le_right t H).trans hH1) a n
  rw [CanonicalProcessTimeRegularity.fourier_clip H a n t]
  rw [← NativeBoundedMartingaleVersion.stop_cap (input a n) t]
  convert hh using 1
  · funext x
    simp only [CanonicalFourierFluctuation.value, state]
    rw [hzero]
    simp only [clock, NNReal.coe_min, min_assoc, min_self]
  · simp only [NNReal.coe_min, CanonicalNativeFourierInput.input]

variable (hRep : ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0),
  CanonicalFourierFluctuation.value (ι:=ι) H a n t=ᵐ[Q]
    (FiniteCylindricalIto.terminalIto
      (CanonicalNativeFourierRecognition.family H Q hBrown).toCoordinates e).integral
      (StoppedItoInputs.stop (filtration H) Q H t
        (CanonicalNativeFourierInput.input hG hβ hβ1 B hb H Q a n)))

include hRep in
theorem martingale_of_representation (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (CanonicalFourierFluctuation.value (ι := ι) H a n) (filtration H) Q := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  exact ConditionalBracket.martingale J (FiniteCylindricalIto.pastLocality P e) (input a n)
    (CanonicalFourierFluctuation.adapted H a n) (hRep a n)

include hRep in
theorem square_of_representation (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (CanonicalFourierDisintegration.square (ι := ι) H hG hβ hβ1 B hb a n) (filtration H) Q := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  have hh := PredictableBracket.square_compensator_martingale J (FiniteCylindricalIto.pastLocality P e)
    (input a n) (CanonicalFourierFluctuation.adapted H a n)
    (hRep a n)
  apply hh.congr
  · intro t
    exact ((CanonicalFourierFluctuation.adapted H a n t).pow 2).sub
      (CanonicalFourierCompensator.adapted H _ _ _ t)
  · intro t
    filter_upwards [CanonicalNativeFourierInput.energy hG hβ hβ1 B hb H Q a n t] with x hx
    exact congrArg (fun v ↦ (CanonicalFourierFluctuation.value H a n t x)^2-v) hx.symm

include hRep in
theorem mixed_of_representation (a : ℂ →L[ℝ] ℝ) (n : ℤ) (i : ι) :
    Martingale (CanonicalFourierDisintegration.mixed H hG hβ hβ1 B hb a n (e i) i) (filtration H) Q := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  have hclip (j : ι) (t : ℝ≥0) : (P).W j t = (P).W j (min t H) := by
    funext x
    change coordinate H j t x = coordinate H j (min t H) x
    simp only [coordinate, clock, NNReal.coe_min, min_assoc, min_self]
  have hh := NativeCrossCompensator.martingale J (FiniteCylindricalIto.pastLocality P e)
    (input a n) (RotatedCylindricalCoordinates.constant (filtration H) Q H (e i))
    (CanonicalFourierFluctuation.value H a n) (coordinate H i)
    (CanonicalFourierFluctuation.adapted H a n) (fun t ↦ (coordinate_adapted H i t).stronglyMeasurable)
    (hRep a n)
    (NativeHorizonCharacteristics.coordinates P e hclip i)
  apply hh.congr
  · intro t
    exact ((CanonicalFourierFluctuation.adapted H a n t).mul
      (coordinate_adapted H i t).stronglyMeasurable).sub (CanonicalFourierCompensator.adapted H _ _ _ t)
  · intro t
    filter_upwards [CanonicalNativeFourierInput.mixed hG hβ hβ1 B hb H Q a n (e i) t] with x hx
    exact congrArg (fun v ↦ CanonicalFourierFluctuation.value H a n t x*coordinate H i t x-v) hx.symm

include hRep in
theorem subgaussian_of_representation (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
    HasSubgaussianMGF (CanonicalFourierFluctuation.value (ι := ι) H a n t)
      (min t H * BoundedFourierInput.cap H B a n ^ 2) Q := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  have hs := NativeBandMoments.increment_subgaussian P e (input a n)
    (BoundedFourierInput.cap H B a n)
    (BoundedFourierInput.input_bound (filtration H) Q H (state H) (state_predictable H) hG hβ hβ1 B hb a n)
    (s := 0) (t := min t H) zero_le (min_le_right _ _)
  simp only [tsub_zero] at hs
  rw [NNReal.coe_min] at hs
  rw [NativeBoundedMartingaleVersion.stop_cap (input a n) t] at hs
  apply hs.congr
  filter_upwards [hRep a n t,
    Lp.coeFn_zero ℝ 2 Q] with x hr hz
  rw [NNReal.coe_zero, StoppedItoInputs.stop_zero, map_zero, hz, Pi.zero_apply, sub_zero]
  exact hr.symm

include hH1 hMild in
theorem martingale (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (CanonicalFourierFluctuation.value (ι := ι) H a n) (filtration H) Q :=
  martingale_of_representation H Q hG hβ hβ1 B hb e hBrown
    (represents H Q hG hβ hβ1 B hb e hBrown hH1 hMild) a n

include hH1 hMild in
theorem square (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (CanonicalFourierDisintegration.square (ι := ι) H hG hβ hβ1 B hb a n) (filtration H) Q :=
  square_of_representation H Q hG hβ hβ1 B hb e hBrown
    (represents H Q hG hβ hβ1 B hb e hBrown hH1 hMild) a n

include hH1 hMild in
theorem mixed (a : ℂ →L[ℝ] ℝ) (n : ℤ) (i : ι) :
    Martingale (CanonicalFourierDisintegration.mixed H hG hβ hβ1 B hb a n (e i) i) (filtration H) Q :=
  mixed_of_representation H Q hG hβ hβ1 B hb e hBrown
    (represents H Q hG hβ hβ1 B hb e hBrown hH1 hMild) a n i

include hH1 hMild in
theorem subgaussian (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
    HasSubgaussianMGF (CanonicalFourierFluctuation.value (ι := ι) H a n t)
      (min t H * BoundedFourierInput.cap H B a n ^ 2) Q :=
  subgaussian_of_representation H Q hG hβ hβ1 B hb e hBrown
    (represents H Q hG hβ hβ1 B hb e hBrown hH1 hMild) a n t

/-- The bounded native Fourier data required for continuation: the
mode, its square and mixed compensators, and a uniform moment source. -/
def Holds : Prop := ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ),
  Martingale (CanonicalFourierFluctuation.value (ι := ι) H a n) (filtration H) Q ∧
  Martingale (CanonicalFourierDisintegration.square (ι := ι) H hG hβ hβ1 B hb a n) (filtration H) Q ∧
  (∀ i, Martingale (CanonicalFourierDisintegration.mixed H hG hβ hβ1 B hb a n (e i) i) (filtration H) Q) ∧
  ∀ t, HasSubgaussianMGF (CanonicalFourierFluctuation.value (ι := ι) H a n t)
    (min t H * BoundedFourierInput.cap H B a n ^ 2) Q

include hRep in
/-- The common martingale, square, mixed and moment proof needs only
an identification with the actual native integral, independent of the horizon. -/
theorem holds_of_representation : Holds H Q hG hβ hβ1 B hb e := by
  intro a n
  exact ⟨martingale_of_representation H Q hG hβ hβ1 B hb e hBrown hRep a n,
    square_of_representation H Q hG hβ hβ1 B hb e hBrown hRep a n,
    mixed_of_representation H Q hG hβ hβ1 B hb e hBrown hRep a n,
    subgaussian_of_representation H Q hG hβ hβ1 B hb e hBrown hRep a n⟩

include hH1 hMild in
theorem holds : Holds H Q hG hβ hβ1 B hb e := by
  intro a n
  exact ⟨martingale H Q hG hβ hβ1 B hb e hBrown hH1 hMild a n,
    square H Q hG hβ hβ1 B hb e hBrown hH1 hMild a n,
    mixed H Q hG hβ hβ1 B hb e hBrown hH1 hMild a n,
    subgaussian H Q hG hβ hβ1 B hb e hBrown hH1 hMild a n⟩

end SHEStochastic.CanonicalMildFourierCharacteristics
