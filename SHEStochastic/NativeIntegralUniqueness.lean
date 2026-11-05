module

public import SHEStochastic.NativeInputEquiv
public import SHEStochastic.PredictableMultiplier
public import SHEStochastic.FiniteCylindricalSimple
public import SHEStochastic.HilbertSimpleInputs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeIntegralUniqueness
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (J : StandardTerminalIto (C := C) (E := ℝ) F μ H) (hlocal : StandardTerminalPastLocality J)

variable (hcoordinate : ∀ (i : ι) (t : ℝ≥0), t ≤ H →
  RawCylindricalCoordinates.value F μ H (e : ι → C) J i t =ᵐ[μ] P.W i t)

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

include hlocal hcoordinate in
/-- Locality and the actual coordinate primitives determine integration
of each basis-valued predictable simple input. All bounded random
coefficients are handled by the existing past-multiplier theorem. -/
theorem basis_simple (i : ι) (V : FiniteScalarIto.Simple F H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    J.integral (NativeInputEquiv.inverse F μ H
      (L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V))) =
        FiniteScalarIto.simpleLp P.toCoordinates i V := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let S := V.val.value.support
  let r := RawCylindricalCoordinates.row F μ H (e : ι → C) i
  choose u hu hJu using fun p : S ↦ PredictableMultiplier.cell J hlocal r p.val.1 p.val.2
    (V.val.le_of_mem_support_value p.val p.property) (V.val.value p.val)
    (V.val.measurable_value p.val).stronglyMeasurable V.val.valueBound V.val.valueBound_nonneg
    (fun sample ↦ by simpa only [Real.norm_eq_abs] using V.val.value_le_valueBound p.val sample)
  have hEach (p : S) : FiniteCylindricalIto.processTransport (u p) =ᵐ[ν]
      (fun q ↦ PredictableSteps.step p.val.1 p.val.2 (V.val.value p.val) q • e i) := by
    apply NativeRowRepresentatives.transport_ae
    · exact (PredictableSteps.step_stronglyMeasurable F p.val.1 p.val.2
        (V.val.measurable_value p.val).stronglyMeasurable).smul stronglyMeasurable_const
    · filter_upwards [hu p, RotatedCylindricalCoordinates.constant_ae F μ H (e i)] with q hq hr
      exact hq.trans (congrArg (fun c ↦ PredictableSteps.step p.val.1 p.val.2 (V.val.value p.val) q • c) hr)
  have hV : FiniteScalarIto.embedding F μ H V =ᵐ[ν] Function.uncurry V.val := by
    simpa only [HilbertSimpleInputs.embedding_scalar] using HilbertSimpleInputs.embedding_ae F μ H V
  have htime : ∀ᵐ q ∂ν, 0 < q.1 :=
    (FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)).mono fun _ hq ↦ hq.1
  have hInput : FiniteCylindricalIto.processTransport (∑ p : S, u p) =
      L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V) := by
    rw [map_sum]
    apply Lp.ext
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun p : S ↦ FiniteCylindricalIto.processTransport (u p)),
      ae_all_iff.mpr hEach, L2HilbertSum.lift_ae ν (ColumnsHilbertSum.unit e i)
        (FiniteScalarIto.embedding F μ H V), hV, htime] with q hsum he hl hv ht
    rw [hsum, hl, hv]
    simp only [Finset.sum_apply, ColumnsHilbertSum.unit, LinearIsometry.toSpanSingleton_apply]
    simp_rw [he]
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.sum_coe_sort S (fun p ↦ PredictableSteps.step p.1 p.2 (V.val.value p) q)]
    change _ = V.val q.1 q.2
    rw [SimpleProcess.apply_eq, Set.indicator_of_notMem (by simpa using ht.ne'), zero_add, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p _
    simp [PredictableSteps.step, Set.indicator_apply]
  have hTerm (p : S) : J.integral (u p) =ᵐ[μ] (fun sample ↦ V.val.value p.val sample *
      (P.W i p.val.2 sample - P.W i p.val.1 sample)) := by
    filter_upwards [hJu p, hcoordinate i p.val.2 (V.property p.val p.property),
      hcoordinate i p.val.1 ((V.val.le_of_mem_support_value p.val p.property).trans (V.property p.val p.property))]
      with sample hp ht hs
    exact hp.trans (congrArg (fun x ↦ V.val.value p.val sample * x) (congrArg₂ (· - ·) ht hs))
  have huSum : NativeInputEquiv.inverse F μ H
      (L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H V)) = ∑ p : S, u p := by
    rw [← hInput, NativeInputEquiv.inverse_transport]
  rw [huSum, map_sum]
  apply Lp.ext
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun p : S ↦ J.integral (u p)),
    ae_all_iff.mpr hTerm, (FiniteScalarIto.memLp_simpleValue P.toCoordinates i V).coeFn_toLp]
    with sample hsum hp hv
  change (FiniteScalarIto.simpleLp P.toCoordinates i V : Ω → ℝ) sample = _ at hv
  rw [hsum, hv]
  simp only [Finset.sum_apply]
  simp_rw [hp]
  rw [Finset.sum_coe_sort S (fun p ↦ V.val.value p sample * (P.W i p.2 sample - P.W i p.1 sample))]
  rfl

include hlocal hcoordinate in
/-- The native integral is uniquely fixed by its coordinate processes
and ordinary past locality. Density supplies equality for every original
predictable L2 input, without an additional transport axiom. -/
theorem integral (u : Process (E := C) F μ H) :
    J.integral u = (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let A := J.integral.comp (NativeInputEquiv.inverse F μ H)
  let B := FiniteCylindricalIto.rawIntegral P.toCoordinates e
  have hs (V : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
      A (FiniteCylindricalIto.simpleEmbedding e V) = B (FiniteCylindricalIto.simpleEmbedding e V) := by
    induction V using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add v w hv hw => rw [map_add, map_add, map_add, hv, hw]
    | single i V =>
      rw [FiniteCylindricalIto.simpleEmbedding_single]
      change J.integral (NativeInputEquiv.inverse F μ H _) = FiniteCylindricalIto.rawIntegral P.toCoordinates e _
      rw [basis_simple P e J hlocal hcoordinate, FiniteCylindricalIto.rawIntegral_unit,
        FiniteScalarIto.rawIsometry_simple]
  have he := congrFun (DenseRange.equalizer (FiniteCylindricalIto.simpleEmbedding_dense e)
    A.continuous B.continuous (funext hs)) (FiniteCylindricalIto.processTransport u)
  change J.integral (NativeInputEquiv.inverse F μ H (FiniteCylindricalIto.processTransport u)) = _ at he
  rw [NativeInputEquiv.inverse_transport] at he
  exact he

end SHEStochastic.NativeIntegralUniqueness
