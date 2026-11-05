module

public import SHEStochastic.NativeEnergy
public import SHEStochastic.HilbertSimplePartition
public import SHEStochastic.ContinuousBracket
public import BrownianMotion.StochasticIntegral.Predictable
public import Mathlib.Topology.Sequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativePredictableEnergy
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "emb" => HilbertSimpleInputs.embedding F μ H

def primitive (u : Lp C 2 νin) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r, (Set.Iio t).indicator (fun r ↦ ‖u (r, ω)‖ ^ 2) r ∂νt

def simplePrimitive (V : HilbertSimpleInputs.bounded (E := C) F H) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r, (Set.Iio t).indicator (fun r ↦ ‖V.val r ω‖ ^ 2) r ∂νt

theorem simplePrimitive_predictable (V : HilbertSimpleInputs.bounded (E := C) F H) :
    IsStronglyPredictable F (simplePrimitive V) := by
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure :=
    ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  haveI : NullSingletonClass νt := by dsimp [MathFin.ItoIntegralCLM.timeMeasure_T]; infer_instance
  apply StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · intro t
    exact PredictableBracket.stronglyMeasurable_primitive (F := F) νt
      (fun p ↦ ‖V.val p.1 p.2‖ ^ 2) (V.val.isStronglyPredictable.norm.pow 2) t
  · intro ω t
    exact (PredictableBracket.continuous_primitive
      (HilbertSimplePartition.path_memLp V ω).norm.integrable_sq).continuousWithinAt

theorem simplePrimitive_error (V : HilbertSimpleInputs.bounded (E := C) F H)
    (u : Lp C 2 νin) (ω : Ω)
    (hu : Integrable (fun r ↦ ‖u (r, ω)‖ ^ 2) νt)
    (hrep : ∀ᵐ r ∂νt, emb V (r, ω) = V.val r ω) (t : ℝ≥0) :
    |simplePrimitive V t ω - primitive u t ω| ≤ NativeEnergy.deviation (emb V) u ω := by
  have hV := (HilbertSimplePartition.path_memLp V ω).norm.integrable_sq
  have he : (∫ r, |‖V.val r ω‖ ^ 2 - ‖u (r, ω)‖ ^ 2| ∂νt) =
      NativeEnergy.deviation (emb V) u ω := by
    apply integral_congr_ae
    filter_upwards [hrep] with r hr
    change |‖V.val r ω‖ ^ 2 - ‖u (r, ω)‖ ^ 2| = _
    rw [hr]
  rw [← he, simplePrimitive, primitive, integral_indicator measurableSet_Iio,
    integral_indicator measurableSet_Iio, ← integral_sub hV.integrableOn hu.integrableOn]
  exact abs_integral_le_integral_abs.trans
    (integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
      (hV.sub hu).abs)

/-- A predictable energy process agrees with the honest time primitive
at every time on one full-measure event. No completion or right
continuity of the original filtration is assumed. -/
theorem exists_version {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ C) (u : Lp C 2 νin) :
    ∃ A : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F A ∧
      ∀ᵐ ω ∂μ, ∀ t, A t ω = primitive u t ω := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((HilbertSimpleInputs.embedding_dense (F := F) (μ := μ) (H := H) e) u)
  choose V hV using hv
  have hVlim : Filter.Tendsto (fun n ↦ emb (V n)) Filter.atTop (𝓝 u) := by
    simpa only [hV] using hlim
  obtain ⟨ns, _, hD⟩ := (NativeEnergy.tendstoInMeasure_deviation hVlim).exists_seq_tendsto_ae
  let A (t : ℝ≥0) (ω : Ω) := Filter.limUnder Filter.atTop
    (fun n : ℕ ↦ simplePrimitive (V (ns n)) t ω)
  have hrep (n : ℕ) : ∀ᵐ ω ∂μ, ∀ᵐ r ∂νt, emb (V n) (r, ω) = (V n).val r ω := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := Prod.instMeasurableSpace
    have hp : (emb (V n) : ℝ≥0 × Ω → C) =ᵐ[(νt).prod μ] Function.uncurry (V n).val :=
      ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) (HilbertSimpleInputs.embedding_ae F μ H (V n))
    exact Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
      (μ := μ) (ν := MathFin.ItoIntegralCLM.timeMeasure_T H)).quasiMeasurePreserving.ae hp)
  refine ⟨A, ?_, ?_⟩
  · exact StronglyMeasurable.limUnder (fun n ↦ simplePrimitive_predictable (V (ns n)))
  · filter_upwards [hD, ae_all_iff.mpr hrep, (NativeEnergy.product_memLp u).norm.integrable_sq.prod_left_ae]
      with ω hDω hrepω huω
    intro t
    have herror : Filter.Tendsto
        (fun n : ℕ ↦ ‖simplePrimitive (V (ns n)) t ω - primitive u t ω‖)
        Filter.atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ by
        rw [Real.norm_eq_abs]
        exact simplePrimitive_error (V (ns n)) u ω huω (hrepω (ns n)) t) hDω
    exact (tendsto_iff_norm_sub_tendsto_zero.mpr herror).limUnder_eq

end SHEStochastic.NativePredictableEnergy
