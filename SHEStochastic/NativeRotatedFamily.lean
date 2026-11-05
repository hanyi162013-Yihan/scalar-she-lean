module

public import SHEStochastic.PredictableRotationLocality
public import SHEStochastic.NativeMartingaleVersion
public import SHEStochastic.NativeTerminalLevy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeRotatedFamily
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω A C ι κ : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [Countable ι] [DecidableEq ι] [Countable κ] [DecidableEq κ]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) (b : HilbertBasis κ ℝ A)
  (Φ : ℝ≥0 × Ω → A →ₗᵢ[ℝ] C)
  (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
    (F.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p ↦ Φ p.1 p.2))

def row (j : κ) : Process (E := C) F μ H :=
  PredictableItoRotation.processIsometry F μ H Φ hΦ (RawCylindricalCoordinates.row F μ H (b : κ → A) j)

theorem row_ae (j : κ) : ∀ᵐ p ∂energyMeasure μ H, row (F := F) (μ := μ) (H := H) b Φ hΦ j p = Φ p (b j) := by
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H Φ hΦ
    (RawCylindricalCoordinates.row F μ H (b : κ → A) j),
    RotatedCylindricalCoordinates.constant_ae F μ H (b j)] with p hp hc
  change row (F := F) (μ := μ) (H := H) b Φ hΦ j p = _
  exact hp.trans (congrArg (Φ p) hc)

/-- Predictable Hilbert isometries produce an actual adapted continuous
Brownian family in the original full filtration. Every coordinate is a
version of the SAME rotated integral, rather than a new noise with only
the same marginal law. -/
theorem exists_family (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ Q : FiniteScalarIto.Family F μ H κ, ∀ j t, Q.W j t =ᵐ[μ]
      (PredictableItoRotation.integral F μ H Φ hΦ
        (FiniteCylindricalIto.terminalIto P.toCoordinates e)).integral
          (StoppedItoInputs.stop F μ H t (RawCylindricalCoordinates.row F μ H (b : κ → A) j)) := by
  choose M hc ha hp hm hr using fun j : κ ↦ NativeMartingaleVersion.exists_version P e hnull (row b Φ hΦ j)
  have hl (n : ℕ) (a : Fin n → κ) : FiniteBrownianLawOn F μ H (fun i ↦ M (a i))
      (fun i j ↦ if a i = a j then 1 else 0) := by
    apply NativeTerminalLevy.finiteBrownianLaw P e (fun i ↦ row b Φ hΦ (a i)) (fun i ↦ M (a i)) _
    · intro t _
      exact ae_all_iff.mpr (fun i ↦ hr (a i) t)
    · filter_upwards [ae_all_iff.mpr (fun i : Fin n ↦ row_ae (F := F) (μ := μ) (H := H) b Φ hΦ (a i))] with p hrows i j
      rw [hrows i, hrows j, (Φ p).inner_map_map]
      exact orthonormal_iff_ite.mp b.orthonormal (a i) (a j)
  let Q : FiniteScalarIto.Family F μ H κ :=
    { W := M
      adapted := fun j t ↦ (ha j t).measurable
      continuous := hc
      law := hl }
  refine ⟨Q, ?_⟩
  intro j t
  change M j t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
    (PredictableItoRotation.processIsometry F μ H Φ hΦ
      (StoppedItoInputs.stop F μ H t (RawCylindricalCoordinates.row F μ H (b : κ → A) j)))
  rw [PredictableRotationLocality.stop]
  exact hr j t

end SHEStochastic.NativeRotatedFamily
