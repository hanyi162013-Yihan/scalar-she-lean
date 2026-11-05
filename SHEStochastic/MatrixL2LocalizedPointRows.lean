module

public import SHEStochastic.NativeMatrixEquation
public import SHEStochastic.MatrixPointInputCongruence
public import SHEStochastic.MatrixPointInputCausality
public import SHEStochastic.NativeRandomStopLocality
public import SHEStochastic.ContinuousNormExit
public import SHEStochastic.BallProjection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixL2LocalizedPointRows
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

def state (K : ℝ≥0) (p : ℝ≥0×Ω) : Physical (d := Fin n) := BallProjection.project K (U p)

include hU in
theorem predictable (K : ℝ≥0) : StronglyMeasurable[F.predictable] (state U K) :=
  (BallProjection.lipschitz K).continuous.comp_stronglyMeasurable hU

theorem norm_bound (K : ℝ≥0) (p : ℝ≥0×Ω) : ‖state U K p‖≤K := BallProjection.norm_le_radius K (U p)

/-- Equality of the actual L2 states gives equality of the nonlinear
covariance fields, despite their separately chosen joint representatives. -/
theorem profile_congr (W : ℝ≥0×Ω → Physical (d := Fin n))
    (hW : StronglyMeasurable[F.predictable] W) (p : ℝ≥0×Ω) (he : U p=W p) :
    (NativeMatrixEquation.profile F G U hU p).value=ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
      (NativeMatrixEquation.profile F G W hW p).value := by
  filter_upwards [(NativeMatrixEquation.data F G U hU p).covariance_ae,
    (NativeMatrixEquation.data F G W hW p).covariance_ae,
    NativeMatrixEquation.coefficient_ae F G U hU p,NativeMatrixEquation.coefficient_ae F G W hW p] with x hu hw hcu hcw
  rw [←hu,←hw,hcu,hcw,he]

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : (H : ℝ)≤1)

def input (K T : ℝ≥0) (hTH : T≤H) (x : HeatCircle) (i : Fin n) : Process (E := Input (d := Fin n)) F μ H :=
  MatrixPointHeatInput.input F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
    (NativeMatrixEquation.profile F G (state U K) (predictable F U hU K)) (fun _ => le_rfl)
    (NativeMatrixEquation.profile_measurable F G (state U K) (predictable F U hU K)) T hTH x i

/-- Actual localized and original Haar inputs agree up to the original
continuous-state L2 exit, including all spatial covariance dependence. -/
theorem agree_before_exit (hc : ∀ ω,Continuous (fun t => U (t,ω))) (N : ℕ)
    (T : ℝ≥0) (hTH : T≤H) (x : HeatCircle) (i : Fin n) :
    ∀ᵐ p ∂energyMeasure μ H,(p.1 : WithTop ℝ≥0)<ContinuousNormExit.exit (fun t ω => U (t,ω)) N p.2 →
      input F G U hU μ H hH (N : ℝ≥0) T hTH x i p=
        MatrixPointHeatInput.input F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
          (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
          (NativeMatrixEquation.profile_measurable F G U hU) T hTH x i p := by
  filter_upwards [MatrixPointHeatInput.input_ae F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
    (NativeMatrixEquation.profile F G (state U (N : ℝ≥0)) (predictable F U hU (N : ℝ≥0))) (fun _ => le_rfl)
    (NativeMatrixEquation.profile_measurable F G (state U (N : ℝ≥0)) (predictable F U hU (N : ℝ≥0))) T hTH x i,
    MatrixPointHeatInput.input_ae F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
      (NativeMatrixEquation.profile_measurable F G U hU) T hTH x i] with p hl ho hbefore
  change input F G U hU μ H hH (N : ℝ≥0) T hTH x i p=_ at hl
  rw [hl,ho]
  apply MatrixPointInputCongruence.row
  apply profile_congr F G (state U (N : ℝ≥0)) (predictable F U hU (N : ℝ≥0)) U hU p
  exact BallProjection.of_norm_le (N : ℝ≥0)
    (ContinuousNormExit.before_bound (fun t ω => U (t,ω)) hc N p.1 p.2 hbefore).le

/-- The original stochastic convolution and its L2 localization agree
before the exit for the SAME Brownian realization. The random-stop
step uses the existing checked square-compensator locality theorem. -/
theorem native_eq_before (hc : ∀ ω,Continuous (fun t => U (t,ω))) (N : ℕ)
    (T : ℝ≥0) (hTH : T≤H) (x : HeatCircle) (i : Fin n)
    (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∀ᵐ ω ∂μ,(T : WithTop ℝ≥0)≤ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω →
      (FiniteCylindricalIto.terminalIto B.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (input F G U hU μ H hH (N : ℝ≥0) T hTH x i) ω=
      (FiniteCylindricalIto.terminalIto B.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (MatrixPointHeatInput.input F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
          (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
          (NativeMatrixEquation.profile_measurable F G U hU) T hTH x i) ω := by
  apply NativeRandomStopLocality.integral_eq_before F μ H
    (FiniteCylindricalIto.terminalIto B.toCoordinates MatrixPredictableHaarRotation.basis)
    (FiniteCylindricalIto.pastLocality B MatrixPredictableHaarRotation.basis)
    (FiniteCylindricalIto.continuousStoppedVersions B MatrixPredictableHaarRotation.basis) hnull
    (input F G U hU μ H hH (N : ℝ≥0) T hTH x i)
    (MatrixPointHeatInput.input F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
      (NativeMatrixEquation.profile_measurable F G U hU) T hTH x i) T
  · exact MatrixPointInputCausality.process_self F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (NativeMatrixEquation.profile F G (state U (N : ℝ≥0)) (predictable F U hU (N : ℝ≥0))) (fun _ => le_rfl)
      (NativeMatrixEquation.profile_measurable F G (state U (N : ℝ≥0)) (predictable F U hU (N : ℝ≥0))) T hTH x i
  · exact MatrixPointInputCausality.process_self F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl) (NativeMatrixEquation.profile_measurable F G U hU) T hTH x i
  · exact ContinuousNormExit.isStoppingTime (fun t ω => U (t,ω)) hc F
      (show IsStronglyPredictable F (fun t ω => U (t,ω)) from hU).stronglyAdapted N
  · exact agree_before_exit F G U hU μ H hH hc N T hTH x i

end SHEStochastic.MatrixL2LocalizedPointRows
