module

public import SHEStochastic.MatrixMildEndpoint
public import SHEStochastic.MatrixPointFieldTightness
public import SHEStochastic.NativeScalarSectionRecognition
public import SHEStochastic.VectorMildPathTightness
public import SHEStochastic.MatrixPointInputCausality
public import SHEStochastic.NativePathInteriorRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixMildPathRecognition
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.FiniteHaar
open SHE.DyadicApproximation MatrixInfiniteHaar HeatParameterCover StoppedPathPasting
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩

variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
    (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) (hH : (H : ℝ) ≤ 1)
    (N : FiniteScalarIto.Family F μ H ((Fin n) × HaarNode))
    (U : ℝ≥0 × Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)
    (u₀ : Physical (d := Fin n)) (hEq : MatrixContinuousMild.Equation G hH N U hU u₀)
    (hH0 : 0 < H) (Y : Ω → (Fin n → C(Parameter,ℝ))) (hY : Measurable Y)
    (hrep : ∀ (p : Parameter) (i : Fin n), (fun ω => Y ω i p) =ᵐ[μ]
      MatrixPointJointMoments.value F μ H (NativeMatrixEquation.cap G)
        (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU)
        (fun _ => le_rfl) hH (NativeMatrixEquation.profile_measurable F G U hU) N p i)

include hrep hY in
/-- The continuous point fields reconstruct the actual nonlinear
vector L2 state at every positive interior time. -/
theorem state_eq_random
    (Z : Ω → Physical (d := Fin n)) (hZ : Measurable Z)
    (hRandom : MatrixRandomMildExistence.Equation G hH N U hU Z) (s : ℝ≥0) (hs0 : 0 < s) (hsH : s < H) :
    (fun ω => U (s,ω)) =ᵐ[μ] fun ω =>
      VectorMildPathTightness.path H hH0 (Z ω) (Y ω) ⟨(s : ℝ),hs0.le,hsH.le⟩ := by
  have hUs : Measurable (fun ω => U (s,ω)) :=
    (hU.mono (predictable_le_product F)).measurable.comp (measurable_const.prodMk measurable_id)
  have hi (i : Fin n) : VectorStateRepresentative.component (fun ω => U (s,ω)) i =ᵐ[μ]
      fun ω => NativeHeatObservation.heat (s : ℝ) (VectorHeat.coordinates (Z ω) i)+
        NativeRemainderObservation.remainder (Y ω i)
          (GlobalHeatParameter.normalized H hH0 ⟨(s : ℝ),hs0.le,hsH.le⟩) := by
    apply NativeScalarSectionRecognition.state_eq_random μ _
      (VectorStateRepresentative.component_measurable _ hUs i)
      (VectorStateRepresentative.component Z i) (VectorStateRepresentative.component_measurable Z hZ i) (show 0 < (s : ℝ) from hs0)
      (fun ω => Y ω i) ((measurable_pi_apply i).comp hY) _
    filter_upwards [MatrixMildEndpoint.point_history_random G hH N U hU Z hRandom s hs0 hsH] with x hx
    let p := GlobalHeatParameter.point H hH0 ⟨(s : ℝ),hs0.le,hsH.le⟩ x
    have ht : GlobalHeatParameter.time H p = s := NNReal.eq (GlobalHeatParameter.time_point H hH0 _ x)
    have hxcenter : HeatParameterCoordinates.center p = x := HeatParameterPullback.center_point _ x
    have hp := hrep p i
    have he : MatrixPointJointMoments.value F μ H (NativeMatrixEquation.cap G)
        (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU)
        (fun _ => le_rfl) hH (NativeMatrixEquation.profile_measurable F G U hU) N p i =
        (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
          (MatrixPointTargetContinuity.process F μ H hH (NativeMatrixEquation.cap G)
            (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU)
            (fun _ => le_rfl) (NativeMatrixEquation.profile_measurable F G U hU) s s hsH.le x i) := by
      unfold MatrixPointJointMoments.value MatrixPointJointMoments.input
      simp only [ht,hxcenter,MatrixPointInputCausality.process_self]
    rw [he] at hp
    filter_upwards [hx,hp] with ω hω hy
    have hc := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hω
    change PredictableScalarField.nativeField (VectorStateRepresentative.component (fun ω => U (s,ω)) i) (ω,x) =
      PhysicalProfile.physicalHeatMean (NativeHeatObservation.embed (VectorHeat.coordinates (Z ω) i)) ((s : ℝ),x)+_ at hc
    exact hc.trans (congrArg (fun z : ℝ =>
      PhysicalProfile.physicalHeatMean (NativeHeatObservation.embed (VectorHeat.coordinates (Z ω) i)) ((s : ℝ),x)+z) hy.symm)
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  apply VectorHeat.coordinates.injective
  apply PiLp.ext
  intro i
  rw [VectorMildPathTightness.component]
  exact hω i


include hrep hY in
/-- Actual vector solution paths and the continuous-field
reconstruction agree on one event, including both time endpoints. -/
theorem path_eq_random
    (Z : Ω → Physical (d := Fin n)) (hZ : Measurable Z)
    (hRandom : MatrixRandomMildExistence.Equation G hH N U hU Z) (hc : ∀ ω, Continuous (fun t => U (t,ω))) :
    NativeContinuousPath.path H (fun t ω => U (t,ω)) hc =ᵐ[μ]
      fun ω => VectorMildPathTightness.path H hH0 (Z ω) (Y ω) := by
  apply NativePathInteriorRecognition.path_eq μ H hH0 _ hc _
  intro s hs0 hsH
  exact state_eq_random G hH N U hU hH0 Y hY hrep Z hZ hRandom s hs0 hsH

include hEq hrep hY in
theorem state_eq (s : ℝ≥0) (hs0 : 0 < s) (hsH : s < H) :
    (fun ω => U (s,ω)) =ᵐ[μ] fun ω =>
      VectorMildPathTightness.path H hH0 u₀ (Y ω) ⟨(s : ℝ),hs0.le,hsH.le⟩ := by
  exact state_eq_random G hH N U hU hH0 Y hY hrep (fun _ => u₀) measurable_const hEq s hs0 hsH

include hEq hrep hY in
theorem path_eq (hc : ∀ ω, Continuous (fun t => U (t,ω))) :
    NativeContinuousPath.path H (fun t ω => U (t,ω)) hc =ᵐ[μ]
      fun ω => VectorMildPathTightness.path H hH0 u₀ (Y ω) := by
  exact path_eq_random G hH N U hU hH0 Y hY hrep (fun _ => u₀) measurable_const hEq hc

end SHEStochastic.MatrixMildPathRecognition
