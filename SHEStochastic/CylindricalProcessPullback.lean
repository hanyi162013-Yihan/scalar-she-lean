module

public import SHEStochastic.CylindricalPullback
public import SHEStochastic.FiniteCylindricalTerminalIto
public import SHE.RawCylindricalCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.CylindricalPullback
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω Ξ ι κ C D : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
  [Countable ι] [DecidableEq ι] [Countable κ] [DecidableEq κ]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΞ}
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}

/-- Literal stopped basis rows commute with a filtered pullback and a
fixed isometric noise inclusion. -/
theorem stopped_basis_ae
    (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ)
    (e : ι → C) (b : κ → D) (L : C →ₗᵢ[ℝ] D)
    (σ : ι → κ) (hb : ∀ i, L (e i) = b (σ i)) (i : ι) (t : ℝ≥0) :
    StoppedItoInputs.stop G ν H t (RawCylindricalCoordinates.row G ν H b (σ i)) =ᵐ[energyMeasure ν H]
      fun p ↦ L (StoppedItoInputs.stop F μ H t
        (RawCylindricalCoordinates.row F μ H e i) (FilteredPullback.timeMap π p)) := by
  have hp : MeasurePreserving (FilteredPullback.timeMap π) (energyMeasure ν H) (energyMeasure μ H) :=
    (MeasurePreserving.id (timeMeasure H)).prod hπ
  filter_upwards [StoppedItoInputs.stop_ae G ν H t (RawCylindricalCoordinates.row G ν H b (σ i)),
    RotatedCylindricalCoordinates.constant_ae G ν H (b (σ i)),
    hp.quasiMeasurePreserving.ae (StoppedItoInputs.stop_ae F μ H t (RawCylindricalCoordinates.row F μ H e i)),
    hp.quasiMeasurePreserving.ae (RotatedCylindricalCoordinates.constant_ae F μ H (e i))]
    with p hg hbg hf hef
  change RotatedCylindricalCoordinates.constant F μ H (e i) (p.1, π p.2) = e i at hef
  rw [hg, hf]
  change (StoppedItoInputs.before t).indicator (RawCylindricalCoordinates.row G ν H b (σ i)) p =
    L ((StoppedItoInputs.before t).indicator (RawCylindricalCoordinates.row F μ H e i)
      (FilteredPullback.timeMap π p))
  by_cases ht : (p.1 : ℝ) < t
  · simpa only [StoppedItoInputs.before, FilteredPullback.timeMap, Set.indicator_apply,
      Set.mem_setOf_eq, ht, ite_true, RawCylindricalCoordinates.row, hbg, hef] using (hb i).symm
  · simp only [StoppedItoInputs.before, FilteredPullback.timeMap, Set.indicator_apply,
      Set.mem_setOf_eq, ht, ite_false, map_zero]

/-- Naturality stated in the original manuscript's raw predictable-L2
interface. Equality of actual rows is enough; clients need not identify
their chosen Lp representatives or construct a separate integral. -/
theorem process_naturality
    (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ) (hfil : ∀ t, @Measurable Ξ Ω (G t) (F t) π)
    (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H κ)
    (e : HilbertBasis ι ℝ C) (b : HilbertBasis κ ℝ D) (L : C →ₗᵢ[ℝ] D)
    (σ : ι → κ) (hb : ∀ i, L (e i) = b (σ i))
    (hW : ∀ i t ξ, Q.W (σ i) t ξ = P.W i t (π ξ))
    (f : Process (E := C) F μ H) (g : Process (E := D) G ν H)
    (hraw : g =ᵐ[energyMeasure ν H] fun p ↦ L (f (FilteredPullback.timeMap π p))) :
    (FiniteCylindricalIto.terminalIto Q.toCoordinates b).integral g =ᵐ[ν]
      fun ξ ↦ (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral f (π ξ) := by
  have hp := FilteredPullback.predictable_map π hfil
  have hr : StronglyMeasurable[G.predictable] (fun p ↦ L (f (FilteredPullback.timeMap π p))) :=
    L.continuous.comp_stronglyMeasurable ((Lp.stronglyMeasurable f).comp_measurable hp)
  have htrim := ae_eq_trim_of_measurable (predictable_le_product G)
    (Lp.stronglyMeasurable g).measurable hr.measurable hraw
  have hle : ae (FiniteScalarIto.inputMeasure G ν H) ≤
      ae ((energyMeasure ν H).trim (predictable_le_product G)) := by
    rw [FilteredScalarIto.processMeasure_eq (𝓖 := G) (μ := ν) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)]
    exact le_rfl
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
  let v := FiniteCylindricalIto.processTransport f
  have heq : FiniteCylindricalIto.processTransport g =
      L2HilbertSum.lift (FiniteScalarIto.inputMeasure G ν H) L (FilteredPullback.input π hπ hfil v) := by
    apply Lp.ext
    filter_upwards [FiniteCylindricalIto.processTransport_ae g, htrim.filter_mono hle,
      L2HilbertSum.lift_ae (FiniteScalarIto.inputMeasure G ν H) L (FilteredPullback.input π hπ hfil v),
      FilteredPullback.input_ae π hπ hfil v,
      (FilteredPullback.input_preserving π hπ hfil).quasiMeasurePreserving.ae
        (FiniteCylindricalIto.processTransport_ae f)] with p hg ht hL hi hf
    change v (FilteredPullback.timeMap π p) = f (FilteredPullback.timeMap π p) at hf
    rw [hg, ht, hL, hi, hf]
  change FiniteCylindricalIto.rawIntegral Q.toCoordinates b (FiniteCylindricalIto.processTransport g) =ᵐ[ν]
    fun ξ ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e v (π ξ)
  rw [heq, integral_naturality π hπ hfil P Q e b L σ hb hW]
  exact FilteredPullback.output_ae π hπ _

end SHEStochastic.CylindricalPullback
