module

public import SHEStochastic.NativeHorizonIntegral
public import SHEStochastic.NativeRotatedFamily
public import SHEStochastic.NativeInputPairing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeHorizonRotation
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω A C ι κ : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [Countable ι] [DecidableEq ι] [Countable κ] [DecidableEq κ]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H K : ℝ≥0} (hKH : K≤H) (b : HilbertBasis κ ℝ A)
  (Φ : ℝ≥0×Ω → A →ₗᵢ[ℝ] C)
  (hΦ : @Measurable ((ℝ≥0×Ω)×A) C (F.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C›
    (fun p => Φ p.1 p.2))

/-- Rotated coordinate inputs agree under literal extension by zero
whenever their stopping time lies in the smaller horizon. -/
theorem input (j : κ) (t : ℝ≥0) (ht : t≤K) :
    NativeHorizonIntegral.input hKH
      (StoppedItoInputs.stop F μ K t (NativeRotatedFamily.row (F := F) (μ := μ) (H := K) b Φ hΦ j))=
      StoppedItoInputs.stop F μ H t (NativeRotatedFamily.row (F := F) (μ := μ) (H := H) b Φ hΦ j) := by
  let r := StoppedItoInputs.stop F μ K t (NativeRotatedFamily.row (F := F) (μ := μ) (H := K) b Φ hΦ j)
  let f : ℝ≥0×Ω → C := (StoppedItoInputs.before (Ω := Ω) t).indicator (fun p => Φ p (b j))
  have hf : @Measurable _ _ F.predictable _ f := by
    letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
    exact (hΦ.comp (measurable_id.prodMk measurable_const)).indicator (StoppedItoInputs.before_measurable F t)
  have hr : r =ᵐ[energyMeasure μ K] f := by
    filter_upwards [StoppedItoInputs.stop_ae F μ K t (NativeRotatedFamily.row (F := F) (μ := μ) (H := K) b Φ hΦ j),
      NativeRotatedFamily.row_ae (F := F) (μ := μ) (H := K) b Φ hΦ j] with p hs hp
    rw [hs]
    by_cases ht : p∈StoppedItoInputs.before (Ω := Ω) t
    · simpa only [f,Set.indicator_of_mem ht] using hp
    · simp only [f,Set.indicator_of_notMem ht]
  have hrm : @Measurable _ _ (DeterministicItoShift.filtration F 0).predictable _ r := by
    rw [NativeHorizonIntegral.filtration_zero]
    exact (Lp.stronglyMeasurable r).measurable
  have hfm : @Measurable _ _ (DeterministicItoShift.filtration F 0).predictable _ f := by
    rw [NativeHorizonIntegral.filtration_zero]
    exact hf
  have he := DeterministicItoShift.extend_ae F μ H 0 K (by simpa using hKH) hrm hfm hr
  apply NativeInputPairing.process_ext
  filter_upwards [NativeHorizonIntegral.input_ae hKH r,he,
    StoppedItoInputs.stop_ae F μ H t (NativeRotatedFamily.row (F := F) (μ := μ) (H := H) b Φ hΦ j),
    NativeRotatedFamily.row_ae (F := F) (μ := μ) (H := H) b Φ hΦ j,
    (Measure.quasiMeasurePreserving_fst (μ := timeMeasure H) (ν := μ)).ae (timeMeasure_ae_mem H)]
    with p hi he hs hp htime
  rw [hi,he,hs]
  have hbig : (StoppedItoInputs.before (Ω := Ω) t).indicator
      (NativeRotatedFamily.row (F := F) (μ := μ) (H := H) b Φ hΦ j) p=f p := by
    by_cases ht : p∈StoppedItoInputs.before (Ω := Ω) t
    · simpa only [f,Set.indicator_of_mem ht] using hp
    · simp only [f,Set.indicator_of_notMem ht]
  rw [hbig]
  by_cases hq : p.1≤K
  · simp only [DeterministicItoShift.extend,DeterministicItoShift.relative,zero_add,tsub_zero,
      if_pos htime.1,if_pos hq]
  · have hnt : p∉StoppedItoInputs.before (Ω := Ω) t := by
      change ¬(p.1 : ℝ)<(t : ℝ)
      exact not_lt_of_ge (by exact_mod_cast ht.trans (le_of_not_ge hq))
    simp only [DeterministicItoShift.extend,zero_add,if_pos htime.1,if_neg hq,f,Set.indicator_of_notMem hnt]

include hKH in
/-- Equal original coordinates produce equal rotated coordinates on
every overlapping finite time window. -/
theorem coordinate (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family F μ K ι)
    (e : HilbertBasis ι ℝ C) (hW : ∀ i t,t≤K → Q.W i t =ᵐ[μ] P.W i t)
    (j : κ) (t : ℝ≥0) (ht : t≤K) :
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral
      (StoppedItoInputs.stop F μ K t (NativeRotatedFamily.row (F := F) (μ := μ) (H := K) b Φ hΦ j))=
    (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F μ H t (NativeRotatedFamily.row (F := F) (μ := μ) (H := H) b Φ hΦ j)) := by
  rw [NativeHorizonIntegral.integral hKH P Q e hW,input hKH b Φ hΦ j t ht]

end SHEStochastic.NativeHorizonRotation
