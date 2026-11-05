module

public import SHEStochastic.NativeContinuationKernel
public import SHEStochastic.JointDriverCharacteristic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeContinuationCharacteristics
open MeasureTheory ProbabilityTheory SHE SHE.DyadicApproximation SHE.FiniteHaar
open StoppedPathPasting GaussianCharacteristicMartingale
open scoped NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0)
  (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]

/-- Brownian information retained by the actual conditional native
solution kernel, independently of how its coefficient is represented. -/
def BrownianInput : Prop :=
  ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q, ∀ d (a : Fin d → ι),
    FiniteBrownianLawOn (CanonicalStateDriverFiltration.filtration H)
      (CanonicalInitialKernel.kernel H Q u) H
      (fun i ↦ CanonicalStateDriverFiltration.coordinate H (a i))
      (fun i j ↦ if a i = a j then 1 else 0)

/-- A conditional Brownian family starts at zero. Together with the
known conditioned state this gives the actual joint matching condition. -/
theorem matching_initial (h : BrownianInput H Q) :
    ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q, ∀ v : ι → ℝ,
      ∀ᵐ y ∂NativeContinuationKernel.joint H Q (u,v), y (origin H) = (u,v) := by
  filter_upwards [h, CanonicalInitialKernel.matching_initial H Q] with u hu hi v
  let P := CanonicalNativeFourierRecognition.family H (CanonicalInitialKernel.kernel H Q u) hu
  apply JointStateDriverPath.continuationKernel_initial H (CanonicalInitialKernel.kernel H Q) (u,v)
  · filter_upwards [hi] with x hx
    simpa [CanonicalStateDriverFiltration.state, CanonicalStateDriverFiltration.clock, origin] using hx
  · filter_upwards [ae_all_iff.mpr fun i ↦ FiniteScalarIto.zero_ae P.toCoordinates i] with x hx i
    have hz : CanonicalStateDriverFiltration.coordinate H i 0 x = 0 := hx i
    simpa [CanonicalStateDriverFiltration.coordinate, CanonicalStateDriverFiltration.clock, origin] using hz

theorem restart_adapted (v : ι → ℝ) (t : Time H) :
    Measurable[CanonicalStateDriverFiltration.filtration H (AdaptedCanonicalPathTests.toNN H t)]
      (fun x : CanonicalFourierFluctuation.Space (ι := ι) H ↦ JointStateDriverPath.restart H v x t) := by
  have hclock : CanonicalStateDriverFiltration.clock H (AdaptedCanonicalPathTests.toNN H t) = t :=
    Subtype.ext (min_eq_left t.property.2)
  have hs := CanonicalStateDriverFiltration.state_adapted (E := RealL2) (ι := ι) H
    (AdaptedCanonicalPathTests.toNN H t)
  have hd (i : ι) := CanonicalStateDriverFiltration.coordinate_adapted (E := RealL2) H i (AdaptedCanonicalPathTests.toNN H t)
  have hh : Measurable[CanonicalStateDriverFiltration.filtration H (AdaptedCanonicalPathTests.toNN H t)]
      (fun x : CanonicalFourierFluctuation.Space (ι := ι) H ↦
        (CanonicalStateDriverFiltration.state H (AdaptedCanonicalPathTests.toNN H t) x,
          fun i ↦ v i+CanonicalStateDriverFiltration.coordinate H i (AdaptedCanonicalPathTests.toNN H t) x)) := by
    letI : MeasurableSpace (CanonicalFourierFluctuation.Space (ι := ι) H) :=
      CanonicalStateDriverFiltration.filtration H (AdaptedCanonicalPathTests.toNN H t)
    exact hs.prodMk (measurable_pi_iff.mpr fun i ↦ measurable_const.add (hd i))
  change Measurable[CanonicalStateDriverFiltration.filtration H (AdaptedCanonicalPathTests.toNN H t)]
    (fun x ↦ (x.1 t, fun i ↦ v i+x.2 i t))
  simpa only [CanonicalStateDriverFiltration.state, CanonicalStateDriverFiltration.coordinate, hclock] using hh

theorem restart_identity
    (hBrown : ∀ d (a : Fin d → ι),
      FiniteBrownianLawOn (CanonicalStateDriverFiltration.filtration H) Q H
        (fun i ↦ CanonicalStateDriverFiltration.coordinate H (a i))
        (fun i j ↦ if a i = a j then 1 else 0))
    (v : ι → ℝ) {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n) :
    PastedCharacteristicMartingale.Identity H (JointDriverCharacteristic.row (V := RealL2) a r)
      (variance a r) (Q.map (JointStateDriverPath.restart H v)) := by
  let P := CanonicalNativeFourierRecognition.family H Q hBrown
  have hclock (t : Time H) : CanonicalStateDriverFiltration.clock H
      (AdaptedCanonicalPathTests.toNN H t) = t :=
    Subtype.ext (min_eq_left t.property.2)
  have hzero : CanonicalStateDriverFiltration.clock H 0 = origin H :=
    Subtype.ext (min_eq_left H.property)
  apply JointDriverCharacteristic.law_identity (CanonicalStateDriverFiltration.filtration H) Q H P
    (JointStateDriverPath.restart H v)
  · exact (JointStateDriverPath.measurable_restart H).comp (measurable_const.prodMk measurable_id)
  · exact restart_adapted H v
  · intro x t i
    change (v i+x.2 i t)-(v i+x.2 i (origin H)) =
      x.2 i (CanonicalStateDriverFiltration.clock H (AdaptedCanonicalPathTests.toNN H t))-
        x.2 i (CanonicalStateDriverFiltration.clock H 0)
    rw [hclock, hzero]
    ring

theorem properties (h : BrownianInput H Q) :
    ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q, ∀ v : ι → ℝ,
      ∀ n (a : Fin n → ι) (r : WordRecursion.State n),
        PastedCharacteristicMartingale.Identity H (JointDriverCharacteristic.row (V := RealL2) a r)
          (variance a r) (NativeContinuationKernel.joint H Q (u,v)) := by
  filter_upwards [h] with u hu v n a r
  rw [NativeContinuationKernel.joint, JointStateDriverPath.continuationKernel_apply]
  exact restart_identity H (CanonicalInitialKernel.kernel H Q u) hu v a r

end SHEStochastic.NativeContinuationCharacteristics
