module

public import SHEStochastic.NativeChangedCoordinates
public import SHEStochastic.SimplePrimitivePairing
public import SHEStochastic.SimultaneousSimpleApproximation
public import SHEStochastic.NativeCrossContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section

namespace SHEStochastic.NativeSimpleTransport
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

/-- Native predictable equality gives equality along almost every sample path. -/
theorem path_ae {E : Type*} (f g : ℝ≥0 × Ω → E) (he : f =ᵐ[νin] g) :
    ∀ᵐ ω ∂μ, ∀ᵐ r ∂νt, f (r, ω) = g (r, ω) := by
  have hp := ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) he
  have hs := (Measure.measurePreserving_swap (μ := μ)
    (ν := MathFin.ItoIntegralCLM.timeMeasure_T H)).quasiMeasurePreserving.ae hp
  exact Measure.ae_ae_of_ae_prod hs

variable (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (u : Process (E := C) F μ H)

local notation "U" => FiniteCylindricalIto.processTransport u
local notation "Pq" => NativeChangedCoordinates.coordinates P e u
local notation "Q" => NativeChangedCoordinates.changedMeasure P e u

/-- The actual changed coordinate has the expected ordinary primitive,
with the same null set for every time before the horizon. -/
theorem coordinate_drift
    (hu : ∀ᵐ ω ∂μ, StochasticExponential.bracket (C := C) F μ H u ω ≤ 1) (i : ι) : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ H →
    (Pq hu).W i t ω = P.W i t ω +
      ∫ r, (Set.Iio t).indicator (fun r ↦ inner ℝ (e i) (U (r, ω))) r ∂νt := by
  have he : (fun p ↦ inner ℝ (RawCylindricalCoordinates.row F μ H (e : ι → C) i p) (u p)) =ᵐ[νin]
      (fun p ↦ inner ℝ (e i) (U p)) := by
    filter_upwards [FiniteCylindricalIto.constantRow_trim_ae e i,
      FiniteCylindricalIto.processTransport_ae u] with p hr ht
    rw [hr, ht]
  filter_upwards [path_ae _ _ he] with ω hω
  intro t htH
  change P.W i t ω + (∫ r, inner ℝ
    (RawCylindricalCoordinates.row F μ H (e : ι → C) i (r, ω)) (u (r, ω))
      ∂timeMeasure (min t H)) = _
  rw [min_eq_left htH, timeMeasure_eq, ← NativeClockIntegral.before H t htH]
  congr 1
  apply integral_congr_ae
  filter_upwards [hω] with r hr
  by_cases ht : r < t <;> simp only [Set.indicator_apply, Set.mem_Iio, ht, ite_true, ite_false]
  exact hr

/-- Time pairing of one basis-valued scalar simple row is the ordinary
increment sum of the basis component of the control. -/
theorem cross_basis_simple (i : ι) (V : FiniteScalarIto.Simple F H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    NativeCrossEnergy.cross
      (L2HilbertSum.lift νin (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V)) U =ᵐ[μ]
      (fun ω ↦ ∑ p ∈ V.val.value.support, V.val.value p ω *
        ((∫ r, (Set.Iio p.2).indicator (fun r ↦ inner ℝ (e i) (U (r, ω))) r ∂νt) -
          (∫ r, (Set.Iio p.1).indicator (fun r ↦ inner ℝ (e i) (U (r, ω))) r ∂νt))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure :=
    ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  haveI : NullSingletonClass νt := by dsimp [MathFin.ItoIntegralCLM.timeMeasure_T]; infer_instance
  have he : (fun p ↦ inner ℝ
      (L2HilbertSum.lift νin (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V) p) (U p)) =ᵐ[νin]
      (fun p ↦ V.val p.1 p.2 * inner ℝ (e i) (U p)) := by
    filter_upwards [L2HilbertSum.lift_ae νin (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V),
      HilbertSimpleInputs.embedding_ae F μ H V] with p hl hv
    simp only [HilbertSimpleInputs.embedding_scalar] at hv
    rw [hl, hv]
    simp only [ColumnsHilbertSum.unit, LinearIsometry.toSpanSingleton_apply, real_inner_smul_left]
    rfl
  have hi := ((NativeEnergy.product_memLp U).integrable (by norm_num)).prod_left_ae
  filter_upwards [path_ae _ _ he, hi] with ω heω hiω
  change (∫ r, inner ℝ
    (L2HilbertSum.lift νin (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V) (r, ω))
      (U (r, ω)) ∂νt) = _
  rw [integral_congr_ae heω]
  exact SimplePrimitivePairing.simple_pairing νt V.val _ (hiω.const_inner (e i)) ω

/-- The change-of-integral identity for one scalar simple coordinate. -/
theorem scalar_simple
    (hu : ∀ᵐ ω ∂μ, StochasticExponential.bracket (C := C) F μ H u ω ≤ 1) (i : ι) (V : FiniteScalarIto.Simple F H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    letI : IsProbabilityMeasure Q := NativeBoundedNovikov.probability_of_cap P e u 1 zero_le_one hu
    FiniteScalarIto.simpleValue (Pq hu) i V =ᵐ[μ]
      (fun ω ↦ FiniteScalarIto.simpleValue P.toCoordinates i V ω +
        NativeCrossEnergy.cross
          (L2HilbertSum.lift νin (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V)) U ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : IsProbabilityMeasure Q := NativeBoundedNovikov.probability_of_cap P e u 1 zero_le_one hu
  filter_upwards [coordinate_drift P e u hu i, cross_basis_simple e u i V] with ω hc hd
  change (∑ p ∈ V.val.value.support, V.val.value p ω * ((Pq hu).W i p.2 ω - (Pq hu).W i p.1 ω)) =
    (∑ p ∈ V.val.value.support, V.val.value p ω * (P.W i p.2 ω - P.W i p.1 ω)) + _
  rw [hd, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hc p.2 (V.property p hp), hc p.1 ((V.val.le_of_mem_support_value p hp).trans (V.property p hp))]
  ring

end SHEStochastic.NativeSimpleTransport
