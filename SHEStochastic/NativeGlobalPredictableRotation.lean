module

public import SHEStochastic.NativeHorizonRotation
public import SHEStochastic.NativeContinuousHorizonGluing
public import SHEStochastic.NativeIntegralUniqueness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeGlobalPredictableRotation
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω A C ι κ : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [Countable ι] [DecidableEq ι] [Countable κ] [DecidableEq κ]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (P : ∀ H : ℝ≥0,FiniteScalarIto.Family F μ H ι)
  (hP : ∀ H K i t,t ≤ min H K → (P H).W i t =ᵐ[μ] (P K).W i t)
  (e : HilbertBasis ι ℝ C) (b : HilbertBasis κ ℝ A)
  (Φ : ℝ≥0×Ω → A →ₗᵢ[ℝ] C)
  (hΦ : @Measurable ((ℝ≥0×Ω)×A) C (F.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C›
    (fun p => Φ p.1 p.2))

include hP in
/-- One predictable rotation of one global Brownian driver yields one
coherent global Brownian driver. All finite-horizon native integrals
are the transported original integrals, with no extra stochastic input. -/
theorem exists_family (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ Q : ∀ H : ℝ≥0,FiniteScalarIto.Family F μ H κ,
      (∀ H K,(Q H).W=(Q K).W) ∧
      ∀ H (u : Process (E := A) F μ H),
        (FiniteCylindricalIto.terminalIto (Q H).toCoordinates b).integral u=
          (FiniteCylindricalIto.terminalIto (P H).toCoordinates e).integral
            (PredictableItoRotation.processIsometry F μ H Φ hΦ u) := by
  choose R hR using fun j : ℕ => NativeRotatedFamily.exists_family
    (P (NativeContinuousHorizonGluing.horizon j)) e b Φ hΦ hnull
  have hr (j : ℕ) (i : κ) (t : ℝ≥0) : (R j).W i t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto (P (NativeContinuousHorizonGluing.horizon j)).toCoordinates e).integral
        (StoppedItoInputs.stop F μ (NativeContinuousHorizonGluing.horizon j) t
          (NativeRotatedFamily.row (F := F) (μ := μ) (H := NativeContinuousHorizonGluing.horizon j) b Φ hΦ i)) := by
    have hh := hR j i t
    change (R j).W i t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto (P (NativeContinuousHorizonGluing.horizon j)).toCoordinates e).integral
        (PredictableItoRotation.processIsometry F μ (NativeContinuousHorizonGluing.horizon j) Φ hΦ
          (StoppedItoInputs.stop F μ (NativeContinuousHorizonGluing.horizon j) t
            (RawCylindricalCoordinates.row F μ (NativeContinuousHorizonGluing.horizon j) (b : κ → A) i))) at hh
    rw [PredictableRotationLocality.stop] at hh
    exact hh
  have hc (i : κ) (j k : ℕ) (t : ℝ≥0)
      (ht : t ≤ min (NativeContinuousHorizonGluing.horizon j) (NativeContinuousHorizonGluing.horizon k)) :
      (R j).W i t =ᵐ[μ] (R k).W i t := by
    have hstep (j k : ℕ) (hjk : NativeContinuousHorizonGluing.horizon j ≤ NativeContinuousHorizonGluing.horizon k)
        (htj : t ≤ NativeContinuousHorizonGluing.horizon j) : (R j).W i t =ᵐ[μ] (R k).W i t := by
      have hh := NativeHorizonRotation.coordinate hjk b Φ hΦ (P _) (P _) e
        (fun a s hs => hP _ _ a s (le_min hs (hs.trans hjk))) i t htj
      have hj := hr j i t
      rw [hh] at hj
      exact hj.trans (hr k i t).symm
    rcases le_total (NativeContinuousHorizonGluing.horizon j) (NativeContinuousHorizonGluing.horizon k) with hjk | hkj
    · exact hstep j k hjk (ht.trans (min_le_left _ _))
    · exact (hstep k j hkj (ht.trans (min_le_right _ _))).symm
  let Q := fun H => NativeContinuousHorizonGluing.family R hc hnull H
  refine ⟨Q,(fun _ _ => rfl),?_⟩
  intro H u
  let J := PredictableItoRotation.integral F μ H Φ hΦ (FiniteCylindricalIto.terminalIto (P H).toCoordinates e)
  have hl : StandardTerminalPastLocality J := PredictableRotationLocality.pastLocality F μ H Φ hΦ _
    (FiniteCylindricalIto.pastLocality (P H) e)
  have hcoord (i : κ) (t : ℝ≥0) (ht : t ≤ H) : RawCylindricalCoordinates.value F μ H (b : κ → A) J i t =ᵐ[μ] (Q H).W i t := by
    let j : ℕ := ⌈H⌉₊
    have hHj : H ≤ NativeContinuousHorizonGluing.horizon j := NativeContinuousHorizonGluing.covering H
    have hq := NativeContinuousHorizonGluing.version R hc i j t (ht.trans hHj)
    have hh := NativeHorizonRotation.coordinate hHj b Φ hΦ (P _) (P H) e
      (fun a s hs => hP _ _ a s (le_min hs (hs.trans hHj))) i t ht
    have hv := hq.trans (hr j i t)
    rw [←hh] at hv
    change NativeContinuousHorizonGluing.value R i t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto (P H).toCoordinates e).integral
        (StoppedItoInputs.stop F μ H t (NativeRotatedFamily.row (F := F) (μ := μ) (H := H) b Φ hΦ i)) at hv
    change (FiniteCylindricalIto.terminalIto (P H).toCoordinates e).integral
      (PredictableItoRotation.processIsometry F μ H Φ hΦ
        (StoppedItoInputs.stop F μ H t (RawCylindricalCoordinates.row F μ H (b : κ → A) i))) =ᵐ[μ] _
    rw [PredictableRotationLocality.stop]
    exact hv.symm
  exact (NativeIntegralUniqueness.integral (Q H) b J hl hcoord u).symm

end SHEStochastic.NativeGlobalPredictableRotation
