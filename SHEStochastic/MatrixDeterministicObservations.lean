module

public import SHEStochastic.MatrixObservationIntegral
public import SHEStochastic.NativeDeterministicRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixDeterministicObservations
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 → Profile d)
    (hUpper : ∀ r, (Q r).upper ≤ U)
    (hQ : Measurable (fun z : ℝ≥0 × AddCircle (1 : ℝ) => (Q z.1).value z.2))
local notation "ν" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

include hQ in
theorem predictable_field :
    @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1.1).value z.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact hQ.comp (((PredictableClock.time_measurable F).comp measurable_fst).prodMk measurable_snd)

def source (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) : Lp (Input (d := d)) 2 ν :=
  FiniteCylindricalIto.processTransport
    (MatrixObservationInput.input F μ H U hU (fun p => Q p.1) (fun p => hUpper p.1)
      (predictable_field F Q hQ) t ht u)

theorem source_ae (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) :
    source F μ H U hU Q hUpper hQ t ht u =ᵐ[ν]
      (fun p : ℝ≥0 × Ω => MatrixCausalHeatRows.row ((t : ℝ)-(p.1 : ℝ)) (Q p.1) u) :=
  MatrixObservationInput.native_ae F μ H U hU _ _ (predictable_field F Q hQ) t ht u

include hQ in
theorem row_measurable (t : ℝ≥0) (u : Physical (d := d)) :
    StronglyMeasurable (fun r : ℝ≥0 => MatrixCausalHeatRows.row ((t : ℝ)-(r : ℝ)) (Q r) u) :=
  (MatrixCausalHeatRows.measurable _ (measurable_const.sub measurable_subtype_coe) Q hQ u).stronglyMeasurable

include hQ in
theorem row_predictable (t : ℝ≥0) (u : Physical (d := d)) :
    StronglyMeasurable[F.predictable]
      (fun p : ℝ≥0 × Ω => MatrixCausalHeatRows.row ((t : ℝ)-(p.1 : ℝ)) (Q p.1) u) :=
  MatrixObservationInput.predictable F _ (predictable_field F Q hQ) t u

theorem source_covariance (t s : ℝ≥0) (ht : t ≤ H) (hs : s ≤ H)
    (u v : Physical (d := d)) :
    inner ℝ (source F μ H U hU Q hUpper hQ t ht u)
      (source F μ H U hU Q hUpper hQ s hs v) =
      ∫ r, if (r : ℝ) < t ∧ (r : ℝ) < s then
        inner ℝ u (VectorHeat.heat ((t : ℝ)-(r : ℝ))
          (multiplier (Q r) ((VectorHeat.heat ((s : ℝ)-(r : ℝ))).adjoint v))) else 0 ∂νt := by
  rw [NativeDeterministicRows.pairing _ _ _ _ (row_measurable Q hQ t u) (row_measurable Q hQ s v)
    (row_predictable F Q hQ t u) (row_predictable F Q hQ s v)
    (source_ae F μ H U hU Q hUpper hQ t ht u) (source_ae F μ H U hU Q hUpper hQ s hs v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    simp only [MatrixCausalHeatRows.cross_pairing, sub_pos]

/-- Joint Gaussian law for all finite vector spatial observations of a
deterministic covariance convolution, using its native infinite Haar inputs. -/
theorem gaussian {n : ℕ} (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ H) (u : Fin n → Physical (d := d)) :
    HasLaw (HilbertGaussianVector.nativeVector N MatrixPredictableHaarRotation.basis
      (fun i => source F μ H U hU Q hUpper hQ (t i) (ht i) (u i)))
      (multivariateGaussian 0 (Matrix.gram ℝ
        (fun i => source F μ H U hU Q hUpper hQ (t i) (ht i) (u i)))) μ := by
  exact NativeDeterministicRows.gaussian N MatrixPredictableHaarRotation.basis _
    (fun i r => MatrixCausalHeatRows.row ((t i : ℝ)-(r : ℝ)) (Q r) (u i))
    (fun i => row_measurable Q hQ (t i) (u i))
    (fun i => row_predictable F Q hQ (t i) (u i))
    (fun i => source_ae F μ H U hU Q hUpper hQ (t i) (ht i) (u i))

/-- The observed random vector is formed directly from the native vector
convolution, rather than chosen as an abstract Gaussian representative. -/
def vector {n : ℕ} (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ H) (u : Fin n → Physical (d := d))
    (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => inner ℝ (u i)
    (NativeMatrixConvolution.value N U hU (fun p => Q p.1) (fun p => hUpper p.1)
      (predictable_field F Q hQ) (t i) (ht i) ω))

theorem vector_ae {n : ℕ} (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ H) (u : Fin n → Physical (d := d)) :
    vector F μ H U hU Q hUpper hQ N t ht u =ᵐ[μ]
      HilbertGaussianVector.nativeVector N MatrixPredictableHaarRotation.basis
        (fun i => source F μ H U hU Q hUpper hQ (t i) (ht i) (u i)) := by
  filter_upwards [ae_all_iff.mpr fun i => MatrixObservationIntegral.observation_ae N U hU
    (fun p => Q p.1) (fun p => hUpper p.1) (predictable_field F Q hQ) (t i) (ht i) (u i)] with ω hω
  apply WithLp.ofLp_injective
  funext i
  exact hω i

theorem vector_gaussian {n : ℕ} (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ H) (u : Fin n → Physical (d := d)) :
    HasLaw (vector F μ H U hU Q hUpper hQ N t ht u)
      (multivariateGaussian 0 (Matrix.gram ℝ
        (fun i => source F μ H U hU Q hUpper hQ (t i) (ht i) (u i)))) μ :=
  (gaussian F μ H U hU Q hUpper hQ N t ht u).congr
    (vector_ae F μ H U hU Q hUpper hQ N t ht u)

end SHEStochastic.MatrixDeterministicObservations
