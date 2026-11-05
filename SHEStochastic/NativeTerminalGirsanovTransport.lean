module

public import SHEStochastic.NativeCylindricalTransport
public import SHEStochastic.NativeTransportLimit
public import SHEStochastic.StandardHilbertItoLift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeTerminalGirsanovTransport
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νμ" => FiniteScalarIto.inputMeasure F μ H

theorem cross_transport (f u : Process (E := C) F μ H) :
    NativeCrossEnergy.cross (FiniteCylindricalIto.processTransport f)
      (FiniteCylindricalIto.processTransport u) =ᵐ[μ]
      (fun ω ↦ ∫ r, inner ℝ (f (r, ω)) (u (r, ω)) ∂timeMeasure H) := by
  have he : (fun p ↦ inner ℝ (FiniteCylindricalIto.processTransport f p)
      (FiniteCylindricalIto.processTransport u p)) =ᵐ[νμ]
      (fun p ↦ inner ℝ (f p) (u p)) := by
    filter_upwards [FiniteCylindricalIto.processTransport_ae f,
      FiniteCylindricalIto.processTransport_ae u] with p hf hu
    rw [hf, hu]
  filter_upwards [NativeSimpleTransport.path_ae _ _ he] with ω hω
  change (∫ r, inner ℝ (FiniteCylindricalIto.processTransport f (r, ω))
    (FiniteCylindricalIto.processTransport u (r, ω)) ∂MathFin.ItoIntegralCLM.timeMeasure_T H) = _
  rw [timeMeasure_eq]
  exact integral_congr_ae hω

/-- Exact scalar change-of-integral field of the original seventh input.
The changed integral reuses the original coordinate integration machinery. -/
theorem standardTerminalGirsanovTransport (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ C) :
    StandardTerminalGirsanovTransport (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
  intro u hu
  let Q := NativeChangedCoordinates.changedMeasure P e u
  letI : IsProbabilityMeasure Q := NativeBoundedNovikov.probability_of_cap P e u 1 zero_le_one hu
  letI : IsProbabilityMeasure (ExponentialChangeMeasure.measure μ
      (fun ω ↦ (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u ω)
      (StochasticExponential.bracket F μ H u)) :=
    NativeBoundedNovikov.probability_of_cap P e u 1 zero_le_one hu
  let K := NativeChangedCoordinates.changedIto P e u hu
  have hac : Q ≪ μ := ExponentialChangeMeasure.changed_absolutelyContinuous _ _ _
  have hrev : μ ≪ Q := ExponentialChangeMeasure.original_absolutelyContinuous _ _ _
    (NativeBoundedNovikov.mean_one_of_cap P e u 1 zero_le_one hu).1
  refine ⟨K, fun f g hfg ↦ ?_⟩
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hinputRev : νμ ≪ FiniteScalarIto.inputMeasure F Q H :=
    ((Measure.AbsolutelyContinuous.refl (MathFin.ItoIntegralCLM.timeMeasure_T H)).prod hrev).trim
      F.predictable_le_prod
  have hfgNative : f =ᵐ[νμ] g := by
    rw [NativeRowRepresentatives.inputMeasure_eq]
    exact ae_eq_trim_of_measurable (predictable_le_product F)
      (Lp.stronglyMeasurable f).measurable (Lp.stronglyMeasurable g).measurable hfg
  have hsame : FiniteCylindricalIto.processTransport f =ᵐ[νμ]
      FiniteCylindricalIto.processTransport g :=
    (FiniteCylindricalIto.processTransport_ae f).trans
      (hfgNative.trans (hinputRev.ae_eq (FiniteCylindricalIto.processTransport_ae g)).symm)
  have ht := NativeTransportLimit.of_simple (F := F) (μ := μ) (η := Q) (H := H) P.toCoordinates
    (NativeChangedCoordinates.coordinates P e u hu) e (FiniteCylindricalIto.processTransport u) hac
    (NativeCylindricalTransport.simple P e u hu)
    (FiniteCylindricalIto.processTransport f) (FiniteCylindricalIto.processTransport g) hsame
  change FiniteCylindricalIto.rawIntegral (NativeChangedCoordinates.coordinates P e u hu) e
    (FiniteCylindricalIto.processTransport g) =ᵐ[Q]
      (fun ω ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.processTransport f) ω +
        ∫ r, inner ℝ (f (r, ω)) (u (r, ω)) ∂timeMeasure H)
  filter_upwards [ht, hac.ae_eq (cross_transport f u)] with ω hω hc
  exact hω.trans (congrArg (fun x ↦
    FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.processTransport f) ω + x) hc)

/-- Complete original cylindrical Girsanov package: full-past finite laws,
scalar integral transport, and the existing compatible Hilbert lift. -/
theorem standardTerminalGirsanov (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) :
    StandardTerminalGirsanov (FiniteCylindricalIto.terminalIto P.toCoordinates e) where
  finiteLaw := NativeTerminalGirsanovLaw.standardTerminalGirsanovLaw P e
  transport := standardTerminalGirsanovTransport P e
  hilbertTransport := by
    intro u hu Q K
    exact SHEStochastic.standardHilbertItoLift K

end SHEStochastic.NativeTerminalGirsanovTransport
