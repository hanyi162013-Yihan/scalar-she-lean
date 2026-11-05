module

public import SHEStochastic.NativeUniformFourierMixed
public import SHEStochastic.PastedHeatProductMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.NativeContinuationProductInput
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open StoppedPathPasting PastedLinearHeatFunctional NativeContinuationFourierInput
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {ι : Type*} [Countable ι] [DecidableEq ι]


theorem covariance_restart (H : ℝ≥0) (v : ι → ℝ) (rate : ℝ) (hrate : 0 ≤ rate)
    (b : BoundedContinuousFunction RealL2 ℝ) (q : ℝ≥0)
    (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    PastedHeatCovariance.value H rate hrate (b.compContinuous ⟨Prod.fst, continuous_fst⟩)
      (JointStateDriverPath.restart H v x) (AdaptedCanonicalPathTests.clock H q) =
      CanonicalFourierCompensator.value H rate hrate b q x := rfl

theorem driver_restart_value (H : ℝ≥0) (v : ι → ℝ) (i : ι) (q : ℝ≥0)
    (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    value H (NativeUniformFourierMixed.driverRow i) 0 (JointStateDriverPath.restart H v x)
      (AdaptedCanonicalPathTests.clock H q) = CanonicalStateDriverFiltration.coordinate H i q x-
        CanonicalStateDriverFiltration.coordinate H i 0 x := by
  have hzero : CanonicalStateDriverFiltration.clock H 0 = origin H := Subtype.ext (min_eq_left H.property)
  change Real.exp (0*(AdaptedCanonicalPathTests.clock H q).val)*(v i+x.2 i (AdaptedCanonicalPathTests.clock H q))-
    (v i+x.2 i (origin H)) = x.2 i (CanonicalStateDriverFiltration.clock H q)-x.2 i (CanonicalStateDriverFiltration.clock H 0)
  rw [hzero]
  simp only [zero_mul, Real.exp_zero, one_mul, AdaptedCanonicalPathTests.clock, CanonicalStateDriverFiltration.clock]
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (H : ℝ≥0) (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

def diagonal (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    BoundedContinuousFunction (JointStateDriverPath.State RealL2 ι) ℝ :=
  (NativeFourierCompensatorValue.diagonal hG hβ hβ1 B hb a n).compContinuous ⟨Prod.fst, continuous_fst⟩

theorem square_restart_value (v : ι → ℝ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (q : ℝ≥0)
    (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    PastedHeatProductFunctional.value H (row a n) (row (ι := ι) a n) ((n : ℝ)^2) ((n : ℝ)^2)
      (by positivity) (diagonal (ι := ι) hG hβ hβ1 B hb a n) (JointStateDriverPath.restart H v x)
      (AdaptedCanonicalPathTests.clock H q) =
    CanonicalFourierDisintegration.square H hG hβ hβ1 B hb a n q x := by
  unfold PastedHeatProductFunctional.value diagonal CanonicalFourierDisintegration.square
  rw [value_restart, covariance_restart]
  apply congrArg₂ (·-·)
  · ring
  · congr 1
    ring

theorem square_restart_identity (h : CanonicalMildFourierCharacteristics.Holds H Q hG hβ hβ1 B hb e)
    (v : ι → ℝ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    PastedHeatProductMartingale.Identity H (row a n) (row (ι := ι) a n) ((n : ℝ)^2) ((n : ℝ)^2)
      (by positivity) (diagonal (ι := ι) hG hβ hβ1 B hb a n) (Q.map (JointStateDriverPath.restart H v)) := by
  apply PastedHeatProductMartingale.source_identity H (row a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2)
    (by positivity) (diagonal hG hβ hβ1 B hb a n) (JointStateDriverPath.restart H v)
    ((JointStateDriverPath.measurable_restart H).comp (measurable_const.prodMk measurable_id)) Q
    (CanonicalStateDriverFiltration.filtration H) (NativeContinuationCharacteristics.restart_adapted H v)
  simpa only [square_restart_value] using (h a n).2.1

def mixed (a : ℂ →L[ℝ] ℝ) (n : ℤ) (i : ι) :
    BoundedContinuousFunction (JointStateDriverPath.State RealL2 ι) ℝ :=
  (NativeFourierCompensatorValue.mixed hG hβ hβ1 B hb a n (e i)).compContinuous ⟨Prod.fst, continuous_fst⟩

theorem mixed_restart_value (v : ι → ℝ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (i : ι) (q : ℝ≥0)
    (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    PastedHeatProductFunctional.value H (row a n) (NativeUniformFourierMixed.driverRow i) ((n : ℝ)^2) 0
      (by positivity) (mixed hG hβ hβ1 B hb e a n i) (JointStateDriverPath.restart H v x)
      (AdaptedCanonicalPathTests.clock H q) =
    CanonicalFourierFluctuation.value H a n q x*(CanonicalStateDriverFiltration.coordinate H i q x-
      CanonicalStateDriverFiltration.coordinate H i 0 x)-NativeFourierMixedTests.compensator hG hβ hβ1 B hb a n (e i) H q x := by
  unfold PastedHeatProductFunctional.value mixed
  rw [value_restart, driver_restart_value, covariance_restart]
  congr 1
  congr 1
  ring

theorem mixed_restart_identity (h : CanonicalMildFourierCharacteristics.Holds H Q hG hβ hβ1 B hb e)
    (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn (CanonicalStateDriverFiltration.filtration H) Q H
      (fun i ↦ CanonicalStateDriverFiltration.coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0))
    (v : ι → ℝ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (i : ι) :
    PastedHeatProductMartingale.Identity H (row a n) (NativeUniformFourierMixed.driverRow i) ((n : ℝ)^2) 0
      (by positivity) (mixed hG hβ hβ1 B hb e a n i) (Q.map (JointStateDriverPath.restart H v)) := by
  let P := CanonicalNativeFourierRecognition.family H Q hBrown
  have ha : StronglyAdapted (CanonicalStateDriverFiltration.filtration H)
      (fun q x ↦ PastedHeatProductFunctional.value H (row a n) (NativeUniformFourierMixed.driverRow i)
        ((n : ℝ)^2) 0 (by positivity) (mixed hG hβ hβ1 B hb e a n i)
        (JointStateDriverPath.restart H v x) (AdaptedCanonicalPathTests.clock H q)) := by
    intro q
    have h0 := (CanonicalStateDriverFiltration.coordinate_adapted (E := RealL2) H i 0).mono
      ((CanonicalStateDriverFiltration.filtration H).mono (show (0 : ℝ≥0) ≤ q from zero_le)) le_rfl
    have hh := (((CanonicalFourierFluctuation.adapted (ι := ι) H a n q).mul
      ((CanonicalStateDriverFiltration.coordinate_adapted H i q).stronglyMeasurable.sub h0.stronglyMeasurable)).sub
        (CanonicalFourierCompensator.adapted (ι := ι) H ((n : ℝ)^2) (sq_nonneg _)
          (NativeFourierCompensatorValue.mixed hG hβ hβ1 B hb a n (e i)) q))
    convert hh using 1
    funext x
    dsimp only
    rw [mixed_restart_value]
    rfl
  apply PastedHeatProductMartingale.source_identity H (row a n) (NativeUniformFourierMixed.driverRow i)
    ((n : ℝ)^2) 0 (by positivity) (mixed hG hβ hβ1 B hb e a n i) (JointStateDriverPath.restart H v)
    ((JointStateDriverPath.measurable_restart H).comp (measurable_const.prodMk measurable_id)) Q
    (CanonicalStateDriverFiltration.filtration H) (NativeContinuationCharacteristics.restart_adapted H v)
  apply ((h a n).2.2.1 i).congr ha
  intro q
  filter_upwards [FiniteScalarIto.zero_ae P.toCoordinates i] with x hx
  simp only [mixed_restart_value, CanonicalFourierDisintegration.mixed]
  rw [show CanonicalStateDriverFiltration.coordinate H i 0 x = 0 from hx, sub_zero]
  rfl

/-- Both product identities survive conditioning and arbitrary
translation of the joining driver, on one initial-state event. -/
theorem properties (hBrown : NativeContinuationCharacteristics.BrownianInput H Q)
    (h : ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q,
      CanonicalMildFourierCharacteristics.Holds H (CanonicalInitialKernel.kernel H Q u) hG hβ hβ1 B hb e) :
    ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q, ∀ v : ι → ℝ, ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ),
      PastedHeatProductMartingale.Identity H (row a n) (row (ι := ι) a n) ((n : ℝ)^2) ((n : ℝ)^2)
        (by positivity) (diagonal (ι := ι) hG hβ hβ1 B hb a n) (NativeContinuationKernel.joint H Q (u,v)) ∧
      ∀ i : ι, PastedHeatProductMartingale.Identity H (row a n) (NativeUniformFourierMixed.driverRow i)
        ((n : ℝ)^2) 0 (by positivity) (mixed hG hβ hβ1 B hb e a n i)
        (NativeContinuationKernel.joint H Q (u,v)) := by
  filter_upwards [h, hBrown] with u hu hbu v a n
  rw [NativeContinuationKernel.joint, JointStateDriverPath.continuationKernel_apply]
  exact ⟨square_restart_identity H (CanonicalInitialKernel.kernel H Q u) hG hβ hβ1 B hb e hu v a n,
    fun i ↦ mixed_restart_identity H (CanonicalInitialKernel.kernel H Q u) hG hβ hβ1 B hb e hu hbu v a n i⟩

end SHEStochastic.NativeContinuationProductInput
