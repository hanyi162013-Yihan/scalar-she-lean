module

public import SHEStochastic.MatrixRandomMildExistence
public import SHEStochastic.MatrixProfileCongruence
public import SHEStochastic.NativeInputPairing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixMildCovarianceCongruence
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : (H : ℝ) ≤ 1)
    (G K : MatrixNonlinearCoefficient.Coefficient d) (hCov : ∀ z,G.covariance z=K.covariance z)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)

include hCov in
theorem profile_ae (p : ℝ≥0×Ω) :
    (NativeMatrixEquation.profile F G U hU p).value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
      (NativeMatrixEquation.profile F K U hU p).value := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  filter_upwards with x
  change G.covariance (MatrixNemytskii.state U hU (p,x))=K.covariance (MatrixNemytskii.state U hU (p,x))
  exact hCov _

include hCov in
/-- The actual analytic Haar input depends only on the covariance,
even when the two coefficient records use different bounds. -/
theorem input_eq (t : ℝ≥0) (ht : t ≤ H) :
    MatrixAnalyticConvolution.input F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl) (NativeMatrixEquation.profile_measurable F G U hU) t ht=
    MatrixAnalyticConvolution.input F μ H hH (NativeMatrixEquation.cap K) (NativeMatrixEquation.cap_nonneg K)
      (NativeMatrixEquation.profile F K U hU) (fun _ => le_rfl) (NativeMatrixEquation.profile_measurable F K U hU) t ht := by
  apply NativeInputPairing.process_ext
  filter_upwards [MatrixAnalyticConvolution.input_ae F μ H hH (NativeMatrixEquation.cap G)
    (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.profile_measurable F G U hU) t ht,
    MatrixAnalyticConvolution.input_ae F μ H hH (NativeMatrixEquation.cap K)
    (NativeMatrixEquation.cap_nonneg K) (NativeMatrixEquation.profile F K U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.profile_measurable F K U hU) t ht] with p hg hk
  rw [hg,hk]
  exact MatrixProfileCongruence.kernel_eq _ _ (profile_ae F G K hCov U hU p) _

include hCov in
/-- Equal square covariances give the identical actual Haar mild equation. -/
theorem equation (N : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode)) (Z : Ω → Physical (d := d))
    (hEq : MatrixRandomMildExistence.Equation G hH N U hU Z) :
    MatrixRandomMildExistence.Equation K hH N U hU Z := by
  intro t ht
  have hv := congrArg (NativeMatrixConvolution.terminalIto N).integral (input_eq F μ H hH G K hCov U hU t ht)
  have he := hEq t ht
  dsimp only [MatrixContinuousMild.field] at he ⊢
  change (fun ω => U (t,ω)) =ᵐ[μ] fun ω => VectorAnalyticHeat.heat t (Z ω)+
    MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
      (NativeMatrixEquation.profile_measurable F G U hU) N t ht ω at he
  rw [show MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl) (NativeMatrixEquation.profile_measurable F G U hU) N t ht=
    MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap K) (NativeMatrixEquation.cap_nonneg K)
      (NativeMatrixEquation.profile F K U hU) (fun _ => le_rfl) (NativeMatrixEquation.profile_measurable F K U hU) N t ht from hv] at he
  exact he

end SHEStochastic.MatrixMildCovarianceCongruence
