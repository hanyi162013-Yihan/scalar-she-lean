module

public import SHEStochastic.BoundedFourierMartingale
public import SHEStochastic.JointCanonicalCylinderRecognition
public import SHEStochastic.CanonicalNativeBrownian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.CanonicalFourierFluctuation
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar
open NativeFourierHeatCoordinate StoppedPathPasting
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology

variable {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0)
  (a : ℂ →L[ℝ] ℝ) (n : ℤ)

abbrev Space := CanonicalContinuousStateDriver.Space (E := RealL2) (ι := ι) H

def value (t : ℝ≥0) (x : Space (ι := ι) H) : ℝ :=
  Real.exp ((min t H : ℝ≥0)*(n : ℝ)^2) *
    coordinate a n (x.1 (CanonicalStateDriverFiltration.clock H t)) - coordinate a n (x.1 (origin H))

theorem continuous (t : ℝ≥0) : Continuous (value (ι := ι) H a n t) :=
  (continuous_const.mul ((coordinate a n).continuous.comp
    ((continuous_eval_const _).comp continuous_fst))).sub
      ((coordinate a n).continuous.comp ((continuous_eval_const _).comp continuous_fst))

theorem adapted : StronglyAdapted (CanonicalStateDriverFiltration.filtration H)
    (value (ι := ι) H a n) := by
  intro t
  let F := CanonicalStateDriverFiltration.filtration (E := RealL2) (ι := ι) H
  have ht := (JointCanonicalCylinderRecognition.adapted (E := RealL2) (ι := ι) H
    (AdaptedCanonicalPathTests.clock H t)).mono
      (F.mono (show AdaptedCanonicalPathTests.toNN H (AdaptedCanonicalPathTests.clock H t) ≤ t
        from min_le_left _ _)) le_rfl
  have h0 := (JointCanonicalCylinderRecognition.adapted (E := RealL2) (ι := ι) H (origin H)).mono
    (F.mono (show AdaptedCanonicalPathTests.toNN H (origin H) ≤ t from zero_le)) le_rfl
  exact ((stronglyMeasurable_const.mul ((coordinate a n).continuous.comp_stronglyMeasurable
    ht.fst.stronglyMeasurable)).sub ((coordinate a n).continuous.comp_stronglyMeasurable
      h0.fst.stronglyMeasurable))

theorem clock_time (t : ℝ≥0) :
    (CanonicalStateDriverFiltration.clock H t).val.toNNReal = min t H := by
  change (min (t : ℝ) (H : ℝ)).toNNReal = min t H
  rw [← NNReal.coe_min, Real.toNNReal_coe]

theorem comp_bundle {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : FiniteScalarIto.Family F μ H ι) (W : ℝ≥0 → Ω → RealL2)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) (ξ : Ω → RealL2)
    (hInitial : W 0 =ᵐ[μ] ξ) (t : ℝ≥0) :
    (value H a n t ∘ CanonicalNativeBrownian.bundle F μ H P W hcW) =ᵐ[μ]
      BoundedFourierMartingale.fluctuation W ξ a n (min t H) := by
  filter_upwards [hInitial] with sample hInitial
  change Real.exp ((min t H : ℝ≥0)*(n : ℝ)^2) *
    coordinate a n (W (0+(CanonicalStateDriverFiltration.clock H t).val.toNNReal) sample) -
      coordinate a n (W (0+(origin H).val.toNNReal) sample) = _
  rw [clock_time H t]
  simp only [zero_add, origin, Real.toNNReal_zero, hInitial]
  rfl

end SHEStochastic.CanonicalFourierFluctuation
