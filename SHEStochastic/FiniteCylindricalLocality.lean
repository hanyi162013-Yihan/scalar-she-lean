module

public import SHEStochastic.FiniteScalarLocality
public import SHEStochastic.NativeBrownianCoordinates
public import SHE.StandardTerminalPastLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FiniteCylindricalIto
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs
open scoped NNReal ENNReal Topology
variable {Ω ι C : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

def eventFactor (A : Set Ω) : Ω → ℝ := A.indicator (fun _ ↦ 1)

theorem eventFactor_measurable (a : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[F a] A) :
    Measurable[F a] (eventFactor A) := measurable_const.indicator hA

theorem eventFactor_bound (A : Set Ω) (ω : Ω) : |eventFactor A ω| ≤ 1 := by
  by_cases h : ω ∈ A <;> simp [eventFactor, h]

def eventScalarCLM (a : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[F a] A) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  FilteredSimpleLocality.smulAdaptedCLM (F := F) H a
    (eventFactor A) (eventFactor_measurable a A hA) 1 (eventFactor_bound A)

theorem coordinate_event (e : HilbertBasis ι ℝ C) (i : ι) (a : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[F a] A) (u : Process (E := C) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    sourceEquiv e (processTransport (eventProcess F μ H a A hA u)) i =
      eventScalarCLM a A hA (sourceEquiv e (processTransport u) i) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  have hle : ae ν ≤ ae ((energyMeasure μ H).trim (predictable_le_product F)) := by
    rw [FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)]
    exact le_rfl
  have hev := ((Lp.memLp u).indicator (eventAfter_measurable F a hA).nullMeasurableSet).coeFn_toLp
  filter_upwards [sourceEquiv_ae e (processTransport (eventProcess F μ H a A hA u)) i,
    processTransport_ae (eventProcess F μ H a A hA u), hev.filter_mono hle,
    FiniteScalarIto.smulAdaptedCLM_ae (F := F) (μ := μ) (H := H) a
      (eventFactor A) (eventFactor_measurable a A hA) 1 (eventFactor_bound A)
      (sourceEquiv e (processTransport u) i),
    sourceEquiv_ae e (processTransport u) i, processTransport_ae u]
      with p hc ht he hs hf hu
  change eventProcess F μ H a A hA u p = (eventAfter a A).indicator u p at he
  change eventScalarCLM a A hA (sourceEquiv e (processTransport u) i) p = _ at hs
  rw [hc, ht, he, hs, hf, hu]
  by_cases ha : a < p.1 <;> by_cases hω : p.2 ∈ A <;>
    simp [MathFin.afterFactor, eventFactor, eventAfter, Set.indicator_apply, ha, hω]

variable (P : FiniteScalarIto.Family F μ H ι)

theorem rawIsometry_event (i : ι) (a : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[F a] A)
    (f : Lp ℝ 2 ν) :
    FiniteScalarIto.rawIsometry P.toCoordinates i (eventScalarCLM a A hA f) =
      MathFin.mulBddCLM μ ((eventFactor_measurable a A hA).mono (F.le a) le_rfl)
        (eventFactor_bound A)
        (FiniteScalarIto.rawIsometry P.toCoordinates i (eventScalarCLM a Set.univ MeasurableSet.univ f)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  simpa only [eventScalarCLM, eventFactor, Set.indicator_univ] using
    FiniteScalarIto.rawIsometry_after_factor P i a
      (eventFactor A) (eventFactor_measurable a A hA) 1 (eventFactor_bound A) f

/-- Deterministic-past event pullout for the SAME native cylindrical
integral. Scalar elementary pullout and density are lifted by the already
constructed countable orthogonal sum. -/
theorem pastLocality (e : HilbertBasis ι ℝ C) : StandardTerminalPastLocality (terminalIto P.toCoordinates e) := by
  intro a A hA u
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let f := processTransport u
  let g := processTransport (eventProcess F μ H a A hA u)
  let r := processTransport (post F μ H a u)
  let L := MathFin.mulBddCLM μ ((eventFactor_measurable a A hA).mono (F.le a) le_rfl)
    (eventFactor_bound A)
  have he (i : ι) : FiniteScalarIto.rawIsometry P.toCoordinates i (sourceEquiv e g i) =
      L (FiniteScalarIto.rawIsometry P.toCoordinates i (sourceEquiv e r i)) := by
    rw [coordinate_event e i a A hA u,
      rawIsometry_event P i a A hA,
      ← coordinate_event e i a Set.univ MeasurableSet.univ u]
    rfl
  have hsum := L.hasSum (rawIntegral_hasSum P.toCoordinates e r)
  have heq : rawIntegral P.toCoordinates e g = L (rawIntegral P.toCoordinates e r) :=
    (rawIntegral_hasSum P.toCoordinates e g).unique (hsum.congr_fun he)
  change rawIntegral P.toCoordinates e g =ᵐ[μ] A.indicator (rawIntegral P.toCoordinates e r)
  rw [heq]
  filter_upwards [MathFin.coeFn_mulBddCLM μ
    ((eventFactor_measurable a A hA).mono (F.le a) le_rfl)
    (eventFactor_bound A) (rawIntegral P.toCoordinates e r)] with ω hω
  rw [hω]
  by_cases ha : ω ∈ A <;> simp [eventFactor, ha]

end SHEStochastic.FiniteCylindricalIto
