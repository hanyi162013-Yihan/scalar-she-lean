module

public import SHEStochastic.CanonicalProcessTimeRegularity
public import SHEStochastic.CanonicalInitialBrownianKernel
public import SHEStochastic.MatrixCanonicalFourierRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixFourierDisintegration
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixFourierCoordinates
open CanonicalStateDriverFiltration CanonicalProcessTimeRegularity
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
local notation "X" => CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×HaarNode) H
local notation "M" => CanonicalLinearFluctuation.value (ι := d×HaarNode) H (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2)

def square (t : ℝ≥0) (x : X) : ℝ :=
  (M t x)^2-
    CanonicalFourierCompensator.value H (2*(n : ℝ)^2) (by positivity)
      (MatrixFourierCompensator.diagonal G hG hβ hβ1 i a n) t x

def mixed (b : Input (d := d)) (k : d×HaarNode) (t : ℝ≥0)
    (x : X) : ℝ :=
  M t x*coordinate H k t x-
    CanonicalFourierCompensator.value H ((n : ℝ)^2) (sq_nonneg _)
      (MatrixFourierCompensator.mixed G hG hβ hβ1 i a n b) t x

theorem square_time (x : X) :
    Continuous (fun t ↦ square H G hG hβ hβ1 i a n t x) :=
  ((CanonicalLinearFluctuation.time H (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2) x).pow 2).sub (compensator H _ _ _ x)

theorem square_clip (t : ℝ≥0) :
    square H G hG hβ hβ1 i a n t = square H G hG hβ hβ1 i a n (min t H) := by
  funext x
  exact congrArg₂ (·-·)
    (congrArg (fun r : ℝ ↦ r^2) (congrFun (CanonicalLinearFluctuation.clip (ι := d×HaarNode) H (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2) t) x))
    (congrFun (compensator_clip H _ _ _ t) x)

theorem mixed_time (b : Input (d := d)) (k : d×HaarNode)
    (x : X) :
    Continuous (fun t ↦ mixed H G hG hβ hβ1 i a n b k t x) :=
  ((CanonicalLinearFluctuation.time H (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2) x).mul (coordinate_continuous H k x)).sub (compensator H _ _ _ x)

theorem mixed_clip (b : Input (d := d)) (k : d×HaarNode) (t : ℝ≥0) :
    mixed H G hG hβ hβ1 i a n b k t = mixed H G hG hβ hβ1 i a n b k (min t H) := by
  have hd : coordinate (E := Physical (d := d)) H k t = coordinate H k (min t H) := by
    funext x
    simp [CanonicalStateDriverFiltration.coordinate, clock, NNReal.coe_min, min_assoc, min_self]
  funext x
  exact congrArg₂ (·-·)
    (congrArg₂ (·*·) (congrFun (CanonicalLinearFluctuation.clip (ι := d×HaarNode) H (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2) t) x) (congrFun hd x))
    (congrFun (compensator_clip H _ _ _ t) x)


variable (Q : Measure (CanonicalContinuousStateDriver.Space
  (E := Physical (d := d)) (ι := d×HaarNode) H)) [IsProbabilityMeasure Q]

/-- The actual matrix Fourier equation survives conditioning at the
initial vector state, in the whole canonical state-and-driver past. -/
public theorem conditional_equation
    (hM : Martingale M (filtration H) Q) (hM2 : ∀ t,MemLp (M t) 2 Q)
    (hS : Martingale (square H G hG hβ hβ1 i a n) (filtration H) Q)
    (hS2 : ∀ t,MemLp (square H G hG hβ hβ1 i a n t) 2 Q)
    (hX : ∀ k,Martingale (mixed H G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k) k) (filtration H) Q)
    (hX2 : ∀ k t,MemLp (mixed H G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k) k t) 2 Q) :
    ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q,
      ∀ hBrown : ∀ m (j : Fin m → d×HaarNode),FiniteBrownianLawOn (filtration H)
        (CanonicalInitialKernel.kernel H Q z) H (fun l => coordinate H (j l))
        (fun l k => if j l=j k then 1 else 0),
      MatrixCanonicalFourierRecognition.Solves H (CanonicalInitialKernel.kernel H Q z)
        G hG hβ hβ1 hBrown i a n := by
  have hm := conditional H Q M hM hM2
    (CanonicalLinearFluctuation.time H (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2))
    (CanonicalLinearFluctuation.clip H (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2))
  have hs := conditional H Q (square H G hG hβ hβ1 i a n) hS hS2
    (square_time H G hG hβ hβ1 i a n) (square_clip H G hG hβ hβ1 i a n)
  have hx (k : d×HaarNode) := conditional H Q
    (mixed H G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k) k) (hX k) (hX2 k)
    (mixed_time H G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k) k)
    (mixed_clip H G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k) k)
  filter_upwards [hm,hs,ae_all_iff.mpr hx] with z hm hs hx hBrown
  exact MatrixCanonicalFourierRecognition.equation H (CanonicalInitialKernel.kernel H Q z)
    G hG hβ hβ1 hBrown i a n hm.1 (fun t _ => hm.2 t) hs.1 (fun k => (hx k).1)

end SHEStochastic.MatrixFourierDisintegration

