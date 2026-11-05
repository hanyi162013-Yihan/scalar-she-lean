module

public import SHEStochastic.MatrixL2LocalizedPointRows
public import SHEStochastic.MatrixPointFieldTightness
public import SHEStochastic.ContinuousFieldBeforeExit
public import SHEStochastic.NativeScalarSectionRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixLocalizedPointField
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (G : MatrixNonlinearCoefficient.Coefficient (Fin n))
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : (H : ℝ)≤1)

def value (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (p : HeatParameterCover.Parameter) (i : Fin n) : Lp ℝ 2 μ :=
  MatrixPointJointMoments.value F μ H (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
    (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl) hH
    (NativeMatrixEquation.profile_measurable F G U hU) B p i

/-- Actual continuous point-field versions agree on one event before
the L2 exit, simultaneously for every heat time and spatial center. -/
theorem agrees (hc : ∀ ω,Continuous (fun t => U (t,ω))) (N : ℕ)
    (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (i : Fin n)
    (Y Z : Ω → C(HeatParameterCover.Parameter,ℝ))
    (hY : ∀ p,(fun ω => Y ω p)=ᵐ[μ]
      value F G (MatrixL2LocalizedPointRows.state U (N : ℝ≥0))
        (MatrixL2LocalizedPointRows.predictable F U hU (N : ℝ≥0)) μ H hH B p i)
    (hZ : ∀ p,(fun ω => Z ω p)=ᵐ[μ] value F G U hU μ H hH B p i) :
    ∀ᵐ ω ∂μ,∀ p,(GlobalHeatParameter.time H p : WithTop ℝ≥0)<
      ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω → Y ω p=Z ω p := by
  apply ContinuousFieldBeforeExit.simultaneous μ (fun p ω => Y ω p) (fun p ω => Z ω p) H
    (ContinuousNormExit.exit (fun t ω => U (t,ω)) N) (GlobalHeatParameter.time H)
    (GlobalHeatParameter.time_lipschitz H).continuous (GlobalHeatParameter.time_le_horizon H)
    (Filter.Eventually.of_forall (fun ω => (Y ω).continuous))
    (Filter.Eventually.of_forall (fun ω => (Z ω).continuous))
  intro p
  have hn := MatrixL2LocalizedPointRows.native_eq_before F G U hU μ H hH hc N
    (GlobalHeatParameter.time H p) (GlobalHeatParameter.time_le_horizon H p)
    (HeatParameterCoordinates.center p) i B hnull
  filter_upwards [hY p,hZ p,hn] with ω hy hz hn hp
  exact hy.trans ((hn hp.le).trans hz.symm)

/-- Equality of the physical point sections identifies their actual
spatial L2 remainders, without point-evaluation conventions for L2. -/
theorem remainder_congr (Y Z : C(HeatParameterCover.Parameter,ℝ))
    (t : HeatParameterPullback.ShortTime)
    (he : ∀ x : HeatCircle,Y (HeatParameterPullback.point t x)=Z (HeatParameterPullback.point t x)) :
    NativeRemainderObservation.remainder Y t=NativeRemainderObservation.remainder Z t := by
  apply NativePhysicalState.push.injective
  apply Lp.ext
  filter_upwards [NativeScalarSectionRecognition.remainder_push_ae Y t,
    NativeScalarSectionRecognition.remainder_push_ae Z t] with x hy hz
  rw [hy,hz,he]

end SHEStochastic.MatrixLocalizedPointField
