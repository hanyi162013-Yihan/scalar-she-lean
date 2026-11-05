module

public import SHE.StandardItoStoppedParameterFubini
public import SHE.StoppedInputContinuity
public import SHEStochastic.LpSections
public import SHEStochastic.AdaptedLpRepresentative
public import SHEStochastic.JointContinuousVersion
public import SHEStochastic.FilteredStoppedIto
public import SHEStochastic.ContinuousStoppedVersions

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

/-- The full stopped parameter-version interface reduces to ordinary
continuous versions for individual integrands. All joint measurability and
simultaneous-time bookkeeping are proved here, without a stochastic Fubini input. -/
theorem standardItoStoppedParameterFubini_of_continuousVersions
    {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [CompleteSpace C] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
    (hcont : NullCompleteFiltration.ContainsNullSets 𝓕 μ → ContinuousStoppedVersions J) :
    SHE.StandardItoStoppedParameterFubini (C := C) (𝓕 := 𝓕) (μ := μ) (H := H) J := by
  intro hnull X _ η _ K raw hraw hK _
  borelize C
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  let ν := (energyMeasure μ H).trim (predictable_le_product 𝓕)
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  letI : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  have htrim (x : X) : K x =ᵐ[ν] fun p ↦ raw (x, p) :=
    ((Lp.stronglyMeasurable (K x)).ae_eq_trim_iff (predictable_le_product 𝓕)
      (hraw.comp_measurable (measurable_const.prodMk measurable_id))).mpr (hK x)
  have hKs : StronglyMeasurable K := LpSections.stronglyMeasurable_of_joint ν K raw hraw htrim
  let G (q : ℝ≥0) (x : X) := J.integral (StoppedItoInputs.stop (C := C) 𝓕 μ H q (K x))
  have hG (q : ℝ≥0) : StronglyMeasurable (G q) :=
    J.integral.continuous.comp_stronglyMeasurable
      ((StoppedInputAlgebra.stop_continuous 𝓕 μ H q).comp_stronglyMeasurable hKs)
  have hGa (q : ℝ≥0) (x : X) : AEStronglyMeasurable[𝓕 q] (G q x : Ω → ℝ) μ := by
    obtain ⟨A, hA, he⟩ := StoppedItoInputs.stopped_integral_adapted 𝓕 μ H J q (K x)
    exact ⟨A, hA, he⟩
  choose Z hZ hZa using (fun q : ℝ≥0 ↦
    AdaptedLpRepresentative.exists_joint μ (𝓕 q) (𝓕.le q) (G q) (hG q) (hGa q))
  choose U hUc hUrep using (fun x : X ↦ hcont hnull (K x))
  obtain ⟨Y, hY, hYa⟩ := JointContinuousVersion.exists_joint 𝓕 μ Z hZ U hUc
    (fun x q ↦ Filter.EventuallyEq.trans (hZa q x) (Filter.EventuallyEq.symm (hUrep x q)))
  refine ⟨Y, hY, Filter.Eventually.of_forall (fun x q ↦ ?_),
    Filter.Eventually.of_forall (fun x ↦ ?_)⟩
  · exact Filter.EventuallyEq.trans ((hYa x).mono (fun _ he ↦ he q)) (hUrep x q)
  · filter_upwards [hYa x] with ω hω
    have he : (fun t ↦ Y (x, (t, ω))) = (fun t ↦ U x t ω) := funext hω
    rw [he]
    exact hUc x ω

/-- The ENTIRE stopped-parameter interface for the constructed real
Brownian integral in an arbitrary full Brownian filtration. -/
theorem filteredScalarStoppedParameterFubini
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [ProbabilityTheory.IsFilteredPreBrownian B 𝓕 μ]
    (hB : ProbabilityTheory.IsPreBrownianReal B μ) (H : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ B t ω)) :
    StandardItoStoppedParameterFubini (FilteredScalarIto.terminalIto (𝓖 := 𝓕) hB H hBmeas) := by
  apply standardItoStoppedParameterFubini_of_continuousVersions
  intro hnull v
  obtain ⟨Y, _, hc, hr⟩ := FilteredScalarIto.exists_continuous_stopped_version
    hB H hBmeas hBcont hnull v
  exact ⟨fun t ω ↦ Y (t, ω), hc, hr⟩

end SHEStochastic
