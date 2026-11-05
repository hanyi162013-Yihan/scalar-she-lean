module

public import SHEStochastic.NativeContinuationCharacteristics
public import SHEStochastic.CanonicalMildFourierCharacteristics
public import SHEStochastic.PastedLinearHeatMartingale
public import SHEStochastic.LinearHeatMaximum
public import SHEStochastic.SubGaussianFourthMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.NativeContinuationFourierInput
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open StoppedPathPasting PastedLinearHeatFunctional
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {ι : Type*} [Countable ι] [DecidableEq ι]

def row (a : ℂ →L[ℝ] ℝ) (n : ℤ) : JointStateDriverPath.State RealL2 ι →L[ℝ] ℝ :=
  (NativeFourierHeatCoordinate.coordinate a n).comp (ContinuousLinearMap.fst ℝ RealL2 (ι → ℝ))

def fourthConstant (H B : ℝ≥0) (a : ℂ →L[ℝ] ℝ) (n : ℤ) : ℝ≥0∞ :=
  4 * ENNReal.ofReal (48*Real.exp (1/2 : ℝ)*(((H*BoundedFourierInput.cap H B a n^2 : ℝ≥0) : ℝ)^2))

theorem fourthConstant_lt_top (H B : ℝ≥0) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    fourthConstant H B a n < ⊤ := ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

theorem value_restart (H : ℝ≥0) (v : ι → ℝ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (q : ℝ≥0)
    (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    value H (row (ι := ι) a n) ((n : ℝ)^2) (JointStateDriverPath.restart H v x)
      (AdaptedCanonicalPathTests.clock H q) = CanonicalFourierFluctuation.value H a n q x := by
  change Real.exp ((n : ℝ)^2*(AdaptedCanonicalPathTests.clock H q).val)*
      NativeFourierHeatCoordinate.coordinate a n (x.1 (AdaptedCanonicalPathTests.clock H q))-
        NativeFourierHeatCoordinate.coordinate a n (x.1 (origin H)) = _
  simp only [AdaptedCanonicalPathTests.clock, CanonicalFourierFluctuation.value,
    CanonicalStateDriverFiltration.clock, NNReal.coe_min, mul_comm]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (H : ℝ≥0) (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

theorem restart_identity (h : CanonicalMildFourierCharacteristics.Holds H Q hG hβ hβ1 B hb e)
    (v : ι → ℝ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    PastedLinearHeatMartingale.Identity H (row (ι := ι) a n) ((n : ℝ)^2)
      (Q.map (JointStateDriverPath.restart H v)) := by
  apply PastedLinearHeatMartingale.source_identity H (row a n) ((n : ℝ)^2)
    (CanonicalStateDriverFiltration.filtration H) Q (JointStateDriverPath.restart H v)
    ((JointStateDriverPath.measurable_restart H).comp (measurable_const.prodMk measurable_id))
    (NativeContinuationCharacteristics.restart_adapted H v)
  simpa only [value_restart] using (h a n).1

theorem restart_fourth (h : CanonicalMildFourierCharacteristics.Holds H Q hG hβ hβ1 B hb e)
    (v : ι → ℝ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    (∫⁻ y, ENNReal.ofReal ((envelope H (row (ι := ι) a n) ((n : ℝ)^2) y)^4)
      ∂Q.map (JointStateDriverPath.restart H v)) ≤ fourthConstant H B a n := by
  let X : CanonicalFourierFluctuation.Space (ι := ι) H → Path H (JointStateDriverPath.State RealL2 ι) :=
    JointStateDriverPath.restart H v
  let M := CanonicalFourierFluctuation.value (ι := ι) H a n
  have hM : Martingale (fun q x ↦ value H (row a n) ((n : ℝ)^2) (X x) (AdaptedCanonicalPathTests.clock H q))
      (CanonicalStateDriverFiltration.filtration H) Q := by simpa only [X, value_restart] using (h a n).1
  have hMom (q : ℝ≥0) : MemLp (fun x ↦ value H (row a n) ((n : ℝ)^2) (X x)
      (AdaptedCanonicalPathTests.clock H q)) 4 Q := by
    simpa only [X, value_restart, show ((4 : ℝ≥0) : ℝ≥0∞) = 4 by norm_num] using
      ((h a n).2.2.2 q).memLp (4 : ℝ≥0)
  have hD := LinearHeatMaximum.fourth_bound H (row a n) ((n : ℝ)^2) Q
    (CanonicalStateDriverFiltration.filtration H) X hM hMom
  simp only [X, value_restart] at hD
  have hs : HasSubgaussianMGF (M H) (H*BoundedFourierInput.cap H B a n^2) Q :=
    by simpa only [min_self] using (h a n).2.2.2 H
  have hi : Integrable (fun x ↦ M H x^4) Q :=
    ((hs.memLp (4 : ℝ≥0)).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)).mono'
      (hs.aestronglyMeasurable.pow 4) (Filter.Eventually.of_forall fun x ↦ by rw [norm_pow])
  have hL : (∫⁻ x, ENNReal.ofReal (M H x^4) ∂Q) ≤
      ENNReal.ofReal (48*Real.exp (1/2 : ℝ)*(((H*BoundedFourierInput.cap H B a n^2 : ℝ≥0) : ℝ)^2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x ↦ by positivity)]
    exact ENNReal.ofReal_le_ofReal (SubGaussianFourthMoment.integral_fourth_le hs)
  have hX : Measurable (JointStateDriverPath.restart H v :
      CanonicalFourierFluctuation.Space (ι := ι) H → Path H (JointStateDriverPath.State RealL2 ι)) :=
    ((JointStateDriverPath.measurable_restart H).comp (measurable_const.prodMk measurable_id))
  rw [lintegral_map ((continuous_envelope H (row (ι := ι) a n) ((n : ℝ)^2)).measurable.pow_const 4).ennreal_ofReal hX]
  exact hD.trans (mul_le_mul_right hL 4)

theorem properties
    (h : ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q,
      CanonicalMildFourierCharacteristics.Holds H (CanonicalInitialKernel.kernel H Q u) hG hβ hβ1 B hb e) :
    ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q, ∀ v : ι → ℝ, ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ),
      PastedLinearHeatMartingale.Identity H (row (ι := ι) a n) ((n : ℝ)^2)
        (NativeContinuationKernel.joint H Q (u,v)) ∧
      (∫⁻ y, ENNReal.ofReal ((envelope H (row (ι := ι) a n) ((n : ℝ)^2) y)^4)
        ∂NativeContinuationKernel.joint H Q (u,v)) ≤ fourthConstant H B a n := by
  filter_upwards [h] with u hu v a n
  rw [NativeContinuationKernel.joint, JointStateDriverPath.continuationKernel_apply]
  exact ⟨restart_identity H (CanonicalInitialKernel.kernel H Q u) hG hβ hβ1 B hb e hu v a n,
    restart_fourth H (CanonicalInitialKernel.kernel H Q u) hG hβ hβ1 B hb e hu v a n⟩

end SHEStochastic.NativeContinuationFourierInput
