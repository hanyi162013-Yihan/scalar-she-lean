module

public import SHEStochastic.NativeGirsanovRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.NativeTerminalGirsanovLaw
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.PastItoInputs
open NativeRowRepresentatives NativeStoppedGram NativeGirsanovRows
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

/-- The exact changed-noise-law part of external package 7, for the
chosen native integral and the original manuscript's stopped versions. -/
theorem standardTerminalGirsanovLaw (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) :
    StandardTerminalGirsanovLaw (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
  intro u hu n R X G _hX _hcontinuous hsame hG
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let U := FiniteCylindricalIto.processTransport u
  have hU : ∀ᵐ ω ∂μ, NativeEnergy.energy U ω ≤ 1 := by
    filter_upwards [NativeBoundedNovikov.energy_transport_ae u, hu] with ω he hω
    rw [he]
    exact hω
  rw [← measure_transport P e u]
  letI : IsProbabilityMeasure (NativeGirsanovTilt.measure P e U) :=
    NativeGirsanovTilt.probability P e U 1 zero_le_one hU
  have hac : NativeGirsanovTilt.measure P e U ≪ μ := by
    unfold NativeGirsanovTilt.measure
    exact withDensity_absolutelyContinuous μ _
  constructor
  · intro t htH
    let S (i : Fin n) := FiniteCylindricalIto.processTransport (stop F μ H (t i) (R i))
    have hSa (i : Fin n) : ∀ᵐ p ∂νin, p.1 ≤ 0 → S i p = 0 := by
      filter_upwards [FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
        (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)] with p hp hz
      exact False.elim ((not_le.mpr hp.1) hz)
    have hl := (NativeGirsanovVector.law_and_independent P e U 1 zero_le_one hU 0 zero_le S hSa
      (stopped_profiles R G hG t)).1
    have hcov := stopped_gram R G hG t htH
    change Matrix.gram ℝ S = _ at hcov
    rw [hcov] at hl
    apply hl.congr
    apply hac.ae_eq
    have he : ∀ᵐ ω ∂μ, ∀ i : Fin n,
        girsanovShift u (R i) (X i) (t i) ω = NativeGirsanovTilt.shift P e U (S i) ω :=
      ae_all_iff.mpr (fun i ↦ shift_stopped P e u (R i) (X i) (t i) (htH i)
        ((hsame (t i) (htH i)).mono fun ω hω ↦ hω i))
    filter_upwards [he] with ω hω
    apply congrArg (WithLp.toLp 2)
    funext i
    exact hω i
  · intro s t hst htH
    let B (i : Fin n) := FiniteCylindricalIto.processTransport (post F μ H s (stop F μ H t (R i)))
    have hBa (i : Fin n) : ∀ᵐ p ∂νin, p.1 ≤ s → B i p = 0 := by
      filter_upwards [band_transport_ae s t (R i)] with p hp hs
      rw [hp]
      exact Set.indicator_of_notMem (fun h ↦ (not_lt.mpr hs) h.1) _
    have hi := (NativeGirsanovVector.law_and_independent P e U 1 zero_le_one hU s (hst.trans htH) B hBa
      (band_profiles R G hG s t)).2
    have hB (i : Fin n) : B i =
        FiniteCylindricalIto.processTransport (stop F μ H t (R i)) -
          FiniteCylindricalIto.processTransport (stop F μ H s (R i)) := by
      dsimp [B]
      rw [PastItoAlgebra.post_stop_eq_sub F μ H s t hst, map_sub]
    have hsub (i : Fin n) : NativeGirsanovTilt.shift P e U (B i) =ᵐ[μ]
        (fun ω ↦ NativeGirsanovTilt.shift P e U
            (FiniteCylindricalIto.processTransport (stop F μ H t (R i))) ω -
          NativeGirsanovTilt.shift P e U
            (FiniteCylindricalIto.processTransport (stop F μ H s (R i))) ω) := by
      rw [hB i]
      exact shift_sub P e U _ _
    have htime (r : ℝ≥0) (hrH : r ≤ H) : ∀ᵐ ω ∂μ, ∀ i : Fin n,
        girsanovShift u (R i) (X i) r ω = NativeGirsanovTilt.shift P e U
          (FiniteCylindricalIto.processTransport (stop F μ H r (R i))) ω :=
      ae_all_iff.mpr (fun i ↦ shift_stopped P e u (R i) (X i) r hrH
        ((hsame r hrH).mono fun ω hω ↦ hω i))
    have he : (fun ω ↦ WithLp.toLp 2 (fun i ↦
        girsanovShift u (R i) (X i) t ω - girsanovShift u (R i) (X i) s ω)) =ᵐ[μ]
        NativeGirsanovVector.vector P e U B := by
      filter_upwards [htime t htH, htime s (hst.trans htH), ae_all_iff.mpr hsub] with ω ht hs hω
      apply congrArg (WithLp.toLp 2)
      funext i
      exact (congrArg₂ (· - ·) (ht i) (hs i)).trans (hω i).symm
    have hii := ConditionalCharacteristic.indep_comap_congr (F s) (hac.ae_eq he) hi
    rw [← BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin n))] at hii
    exact hii

end SHEStochastic.NativeTerminalGirsanovLaw
