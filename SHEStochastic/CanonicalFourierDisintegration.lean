module

public import SHEStochastic.CanonicalProcessTimeRegularity
public import SHEStochastic.CanonicalNativeFourierRecognition
public import SHEStochastic.QuadraticMomentBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.CanonicalFourierDisintegration
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open CanonicalStateDriverFiltration CanonicalProcessTimeRegularity
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
  (H : ℝ≥0) {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

def square (t : ℝ≥0) (x : CanonicalFourierFluctuation.Space (ι := ι) H) : ℝ :=
  (CanonicalFourierFluctuation.value H a n t x)^2-
    CanonicalFourierCompensator.value H (2*(n : ℝ)^2) (by positivity)
      (NativeFourierCompensatorValue.diagonal hG hβ hβ1 B hb a n) t x

def mixed (b : Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (i : ι) (t : ℝ≥0)
    (x : CanonicalFourierFluctuation.Space (ι := ι) H) : ℝ :=
  CanonicalFourierFluctuation.value H a n t x*coordinate H i t x-
    CanonicalFourierCompensator.value H ((n : ℝ)^2) (sq_nonneg _)
      (NativeFourierCompensatorValue.mixed hG hβ hβ1 B hb a n b) t x

theorem square_time (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    Continuous (fun t ↦ square H hG hβ hβ1 B hb a n t x) :=
  ((fourier H a n x).pow 2).sub (compensator H _ _ _ x)

theorem square_clip (t : ℝ≥0) :
    square (ι := ι) H hG hβ hβ1 B hb a n t = square H hG hβ hβ1 B hb a n (min t H) := by
  funext x
  exact congrArg₂ (·-·)
    (congrArg (fun r : ℝ ↦ r^2) (congrFun (fourier_clip (ι := ι) H a n t) x))
    (congrFun (compensator_clip H _ _ _ t) x)

theorem mixed_time (b : Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (i : ι)
    (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    Continuous (fun t ↦ mixed H hG hβ hβ1 B hb a n b i t x) :=
  ((fourier H a n x).mul (coordinate_continuous H i x)).sub (compensator H _ _ _ x)

theorem mixed_clip (b : Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (i : ι) (t : ℝ≥0) :
    mixed H hG hβ hβ1 B hb a n b i t = mixed H hG hβ hβ1 B hb a n b i (min t H) := by
  have hd : coordinate (E := RealL2) H i t = coordinate H i (min t H) := by
    funext x
    simp [coordinate, clock, NNReal.coe_min, min_assoc, min_self]
  funext x
  exact congrArg₂ (·-·)
    (congrArg₂ (·*·) (congrFun (fourier_clip H a n t) x) (congrFun hd x))
    (congrFun (compensator_clip H _ _ _ t) x)

variable (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

theorem coordinate_subgaussian
    (hBrown : ∀ d (j : Fin d → ι), FiniteBrownianLawOn (filtration H) Q H
      (fun i ↦ coordinate H (j i)) (fun i k ↦ if j i = j k then 1 else 0)) (i : ι) (t : ℝ≥0) :
    HasSubgaussianMGF (coordinate (E := RealL2) H i t) (min t H) Q := by
  have hl := BrownianCoordinates.eval_law (filtration H) Q H (coordinate H) hBrown
    i (min t H) (min_le_right _ _)
  have he : coordinate (E := RealL2) H i (min t H) = coordinate H i t := by
    funext x
    simp [coordinate, clock, NNReal.coe_min, min_assoc, min_self]
  rw [he] at hl
  exact CanonicalBrownianSubGaussian.of_law Q (min t H) hl

/-- The Fourier equation, including its actual stochastic integral,
survives disintegration at the initial state. Only ordinary source
martingales and their L2 moments are used as premises. -/
theorem equation
    (hM : Martingale (CanonicalFourierFluctuation.value H a n) (filtration H) Q)
    (hM2 : ∀ t, MemLp (CanonicalFourierFluctuation.value H a n t) 2 Q)
    (hS : Martingale (square H hG hβ hβ1 B hb a n) (filtration H) Q)
    (hS2 : ∀ t, MemLp (square H hG hβ hβ1 B hb a n t) 2 Q)
    (hX : ∀ i, Martingale (mixed H hG hβ hβ1 B hb a n (e i) i) (filtration H) Q)
    (hX2 : ∀ i t, MemLp (mixed H hG hβ hβ1 B hb a n (e i) i t) 2 Q) :
    ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q,
      ∀ hBrown : ∀ d (j : Fin d → ι), FiniteBrownianLawOn (filtration H)
        (CanonicalInitialKernel.kernel H Q z) H (fun i ↦ coordinate H (j i))
        (fun i k ↦ if j i = j k then 1 else 0),
      CanonicalNativeFourierRecognition.Solves H (CanonicalInitialKernel.kernel H Q z)
        hG hβ hβ1 B hb e hBrown a n := by
  have hm := conditional H Q (CanonicalFourierFluctuation.value H a n) hM hM2
    (fourier H a n) (fourier_clip H a n)
  have hs := conditional H Q (square H hG hβ hβ1 B hb a n) hS hS2
    (square_time H hG hβ hβ1 B hb a n) (square_clip H hG hβ hβ1 B hb a n)
  have hx (i : ι) := conditional H Q (mixed H hG hβ hβ1 B hb a n (e i) i) (hX i) (hX2 i)
    (mixed_time H hG hβ hβ1 B hb a n (e i) i) (mixed_clip H hG hβ hβ1 B hb a n (e i) i)
  filter_upwards [hm, hs, ae_all_iff.mpr hx] with z hm hs hx hBrown
  exact CanonicalNativeFourierRecognition.equation H (CanonicalInitialKernel.kernel H Q z)
    hG hβ hβ1 B hb e hBrown a n hm.1 (fun t _ ↦ hm.2 t) hs.1 (fun i ↦ (hx i).1)

end SHEStochastic.CanonicalFourierDisintegration
