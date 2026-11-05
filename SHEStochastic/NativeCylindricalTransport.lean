module

public import SHEStochastic.NativeSimpleTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeCylindricalTransport
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

private theorem cross_zero (u : Lp C 2 νin) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    NativeCrossEnergy.cross (0 : Lp C 2 νin) u =ᵐ[μ] (fun _ ↦ 0) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  filter_upwards [NativeSimpleTransport.path_ae _ _ (Lp.coeFn_zero C 2 νin)] with ω hω
  change (∫ r, inner ℝ ((0 : Lp C 2 νin) (r, ω)) (u (r, ω))
    ∂MathFin.ItoIntegralCLM.timeMeasure_T H) = 0
  apply integral_eq_zero_of_ae
  exact hω.mono fun r hr ↦ by
    change inner ℝ ((0 : Lp C 2 νin) (r, ω)) (u (r, ω)) = 0
    change (0 : Lp C 2 νin) (r, ω) = 0 at hr
    rw [hr, inner_zero_left]

private theorem cross_add (v w u : Lp C 2 νin) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    NativeCrossEnergy.cross (v + w) u =ᵐ[μ]
      (fun ω ↦ NativeCrossEnergy.cross v u ω + NativeCrossEnergy.cross w u ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hh := NativeCrossEnergy.cross_sub (v + w) v u
  simp only [add_sub_cancel_left] at hh
  filter_upwards [hh] with ω hω
  linarith

variable (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (u : Process (E := C) F μ H)
local notation "U" => FiniteCylindricalIto.processTransport u
local notation "Pq" => NativeChangedCoordinates.coordinates P e u
local notation "Q" => NativeChangedCoordinates.changedMeasure P e u

/-- Transport for all finite-coordinate bounded simple inputs, obtained
from the scalar primitive identity by finite linearity. -/
theorem simple
    (hu : ∀ᵐ ω ∂μ, StochasticExponential.bracket (C := C) F μ H u ω ≤ 1) (V : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    letI : IsProbabilityMeasure Q := NativeBoundedNovikov.probability_of_cap P e u 1 zero_le_one hu
    FiniteCylindricalIto.rawIntegral (Pq hu) e (FiniteCylindricalIto.simpleEmbedding (μ := Q) e V) =ᵐ[Q]
      (fun ω ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e
        (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V) ω +
          NativeCrossEnergy.cross (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V) U ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : IsProbabilityMeasure Q := NativeBoundedNovikov.probability_of_cap P e u 1 zero_le_one hu
  have hac : Q ≪ μ := ExponentialChangeMeasure.changed_absolutelyContinuous _ _ _
  induction V using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 Q, hac.ae_eq (Lp.coeFn_zero ℝ 2 μ),
      hac.ae_eq (cross_zero U)] with ω hq hp hc
    rw [hq, hp, hc, add_zero]
  | single i v =>
    simp only [FiniteCylindricalIto.simpleEmbedding_single,
      FiniteCylindricalIto.rawIntegral_unit, FiniteScalarIto.rawIsometry_simple]
    filter_upwards [(FiniteScalarIto.memLp_simpleValue (Pq hu) i v).coeFn_toLp,
      hac.ae_eq (FiniteScalarIto.memLp_simpleValue P.toCoordinates i v).coeFn_toLp,
      hac.ae_eq (NativeSimpleTransport.scalar_simple P e u hu i v)] with ω hq hp hs
    change FiniteScalarIto.simpleLp (Pq hu) i v ω = _ at hq
    change FiniteScalarIto.simpleLp P.toCoordinates i v ω = _ at hp
    rw [hq, hp]
    exact hs
  | add V W hV hW =>
    simp only [map_add]
    filter_upwards [Lp.coeFn_add
        (FiniteCylindricalIto.rawIntegral (Pq hu) e (FiniteCylindricalIto.simpleEmbedding (μ := Q) e V))
        (FiniteCylindricalIto.rawIntegral (Pq hu) e (FiniteCylindricalIto.simpleEmbedding (μ := Q) e W)),
      hac.ae_eq (Lp.coeFn_add
        (FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V))
        (FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.simpleEmbedding (μ := μ) e W))),
      hac.ae_eq (cross_add (FiniteCylindricalIto.simpleEmbedding (μ := μ) e V)
        (FiniteCylindricalIto.simpleEmbedding (μ := μ) e W) U), hV, hW] with ω hq hp hc hv hw
    simp only [Pi.add_apply] at hq hp
    rw [hq, hp, hc, hv, hw]
    ring

end SHEStochastic.NativeCylindricalTransport
