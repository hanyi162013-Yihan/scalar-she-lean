module

public import SHEStochastic.MatrixLocalizedPointField
public import SHEStochastic.MatrixMildPathRecognition
public import SHEStochastic.VectorMildPathEnvelope
public import SHEStochastic.ContinuousPathBeforeExit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixLocalizedMildPath
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar
open StoppedPathPasting AdaptedCanonicalPathTests HeatParameterCover HeatParameterPullback
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

/-- Identical scalar physical sections identify the reconstructed
full-vector mild state at that time. -/
theorem sections_eq (H : ℝ≥0) (hH : 0<H) (ξ : Physical (d := Fin n))
    (Y Z : Fin n → C(Parameter,ℝ)) (t : Time H)
    (he : ∀ i x,Y i (GlobalHeatParameter.point H hH t x)=Z i (GlobalHeatParameter.point H hH t x)) :
    VectorMildPathTightness.path H hH ξ Y t=VectorMildPathTightness.path H hH ξ Z t := by
  apply VectorHeat.coordinates.injective
  apply PiLp.ext
  intro i
  rw [VectorMildPathTightness.component,VectorMildPathTightness.component]
  congr 1
  exact MatrixLocalizedPointField.remainder_congr (Y i) (Z i) (GlobalHeatParameter.normalized H hH t) (he i)

/-- The reconstructed state starts from precisely the given L2 state,
using the proved zero trace of the native convolution. -/
theorem initial (H : ℝ≥0) (hH : 0<H) (ξ : Physical (d := Fin n))
    (Y : Fin n → C(Parameter,ℝ)) (hz : ∀ i p,Y i (HeatParameterCoordinates.zeroTime p)=0) :
    VectorMildPathTightness.path H hH ξ Y (origin H)=ξ := by
  have ht : GlobalHeatParameter.normalized H hH (origin H)=initialTime := by
    apply Subtype.ext
    simp only [GlobalHeatParameter.normalized,origin,zero_div,initialTime]
  apply VectorHeat.coordinates.injective
  apply PiLp.ext
  intro i
  rw [VectorMildPathTightness.component,ht]
  change NativeHeatObservation.heat 0 (VectorHeat.coordinates ξ i)+
    NativePhysicalState.pull (PhysicalHeatParameterSection.value 2 (Y i) initialTime)=_
  rw [PhysicalHeatParameterSection.value_initial 2 (Y i) (hz i),map_zero,add_zero]
  change RealHeat.realHeat (0/NativeHeatObservation.timeScale) (VectorHeat.coordinates ξ i)=_
  rw [zero_div,RealHeat.realHeat_zero]
  rfl

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H)

/-- Continuous localized and original point fields reconstruct the same
mild path up to AND INCLUDING the L2 exit, on one event. -/
theorem agrees (hc : ∀ ω,Continuous (fun t => U (t,ω))) (N : ℕ)
    (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (ξ : Ω → Physical (d := Fin n))
    (Y Z : Ω → (Fin n → C(Parameter,ℝ)))
    (hY : ∀ p i,(fun ω => Y ω i p)=ᵐ[μ]
      MatrixLocalizedPointField.value F G (MatrixL2LocalizedPointRows.state U (N : ℝ≥0))
        (MatrixL2LocalizedPointRows.predictable F U hU (N : ℝ≥0)) μ H hH B p i)
    (hZ : ∀ p i,(fun ω => Z ω i p)=ᵐ[μ] MatrixLocalizedPointField.value F G U hU μ H hH B p i)
    (hzY : ∀ᵐ ω ∂μ,∀ i p,Y ω i (HeatParameterCoordinates.zeroTime p)=0)
    (hzZ : ∀ᵐ ω ∂μ,∀ i p,Z ω i (HeatParameterCoordinates.zeroTime p)=0) :
    ∀ᵐ ω ∂μ,∀ t : Time H,(toNN H t : WithTop ℝ≥0)≤ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω →
      VectorMildPathTightness.path H hH0 (ξ ω) (Y ω) t=VectorMildPathTightness.path H hH0 (ξ ω) (Z ω) t := by
  have hf : ∀ᵐ ω ∂μ,∀ i p,(GlobalHeatParameter.time H p : WithTop ℝ≥0)<
      ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω → Y ω i p=Z ω i p :=
    ae_all_iff.mpr (fun i => MatrixLocalizedPointField.agrees F G U hU μ H hH hc N B hnull i
      (fun ω => Y ω i) (fun ω => Z ω i) (fun p => hY p i) (fun p => hZ p i))
  apply ContinuousPathBeforeExit.closed μ H
    (fun ω => VectorMildPathTightness.path H hH0 (ξ ω) (Y ω))
    (fun ω => VectorMildPathTightness.path H hH0 (ξ ω) (Z ω))
    (ContinuousNormExit.exit (fun t ω => U (t,ω)) N)
  · filter_upwards [hzY,hzZ] with ω hy hz
    rw [initial H hH0 (ξ ω) (Y ω) hy,initial H hH0 (ξ ω) (Z ω) hz]
  · filter_upwards [hf] with ω hω t ht
    apply sections_eq H hH0 (ξ ω) (Y ω) (Z ω) t
    intro i x
    apply hω i (GlobalHeatParameter.point H hH0 t x)
    have he : GlobalHeatParameter.time H (GlobalHeatParameter.point H hH0 t x)=toNN H t :=
      NNReal.eq (GlobalHeatParameter.time_point H hH0 t x)
    rw [he]
    exact ht

/-- An actual bounded-cutoff mild solution is its localized-field
reconstruction through its L2 exit. No localized SPDE equation is
assumed, and the Brownian realization is unchanged. -/
theorem state_before (hc : ∀ ω,Continuous (fun t => U (t,ω))) (N : ℕ)
    (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → Physical (d := Fin n)) (hξ : Measurable ξ)
    (hEq : MatrixRandomMildExistence.Equation G hH B U hU ξ)
    (Y : Ω → (Fin n → C(Parameter,ℝ)))
    (hY : ∀ p i,(fun ω => Y ω i p)=ᵐ[μ]
      MatrixLocalizedPointField.value F G (MatrixL2LocalizedPointRows.state U (N : ℝ≥0))
        (MatrixL2LocalizedPointRows.predictable F U hU (N : ℝ≥0)) μ H hH B p i)
    (hzY : ∀ᵐ ω ∂μ,∀ i p,Y ω i (HeatParameterCoordinates.zeroTime p)=0) :
    ∀ᵐ ω ∂μ,∀ t : Time H,(toNN H t : WithTop ℝ≥0)≤ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω →
      U (toNN H t,ω)=VectorMildPathTightness.path H hH0 (ξ ω) (Y ω) t := by
  choose Z hm he hz using fun i : Fin n => MatrixPointFieldTightness.exists_version F μ H
    (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU)
    (fun _ => le_rfl) hH (NativeMatrixEquation.profile_measurable F G U hU) B i
  let ZZ := fun ω i => Z i ω
  have hmZ : Measurable ZZ := measurable_pi_iff.mpr hm
  have hp := MatrixMildPathRecognition.path_eq_random G hH B U hU hH0 ZZ hmZ
    (fun p i => he i p) ξ hξ hEq hc
  have ha := agrees F G U hU μ H hH hH0 hc N B hnull ξ Y ZZ hY (fun p i => he i p)
    hzY (ae_all_iff.mpr hz)
  filter_upwards [hp,ha] with ω hp ha t ht
  have he := congrArg (fun z : Path H (Physical (d := Fin n)) => z t) hp
  rw [NativeContinuousPath.path_apply] at he
  have htime : t.val.toNNReal=toNN H t := by
    change t.val.toNNReal=⟨t.val,t.property.1⟩
    exact Real.toNNReal_of_nonneg t.property.1
  rw [htime] at he
  exact he.trans (ha t ht).symm

end SHEStochastic.MatrixLocalizedMildPath
