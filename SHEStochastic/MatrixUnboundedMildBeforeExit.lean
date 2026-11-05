module

public import SHEStochastic.MatrixUnboundedCompletedRemainder
public import SHEStochastic.MatrixUnboundedLocalFourierConvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixUnboundedMildBeforeExit
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar HeatParameterCover HeatParameterCoordinates HeatParameterPullback GlobalHeatRowPhysicalIntegration
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) := borel _
local instance : BorelSpace
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  MatrixUnboundedCompletedGlobal.completedSigma S

/-- The continuous physical stochastic convolution and the global
Hilbert remainder have identical Fourier tests strictly before exit. -/
theorem coordinate (H : ℝ≥0) (hH : 0<H) (N : ℕ) (i : Fin n)
    (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ ω ∂μc,
      (H : WithTop ℝ≥0) < ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
      MatrixFourierCoordinates.coordinate i a m
        (MatrixUnboundedContinuousConvolution.physical S H (unitTime H hH H le_rfl) ω) =
      MatrixFourierCoordinates.coordinate i a m
        (MatrixUnboundedCompletedRemainder.value S H ω) := by
  have hl := MatrixUnboundedLocalFourierConvolution.coordinate S H hH i N H le_rfl a m
  have hn := MatrixUnboundedCompletedExitIto.native_integral_eq S H N i a m
  have hg := MatrixUnboundedCompletedRemainder.fourier_coordinate S H i a m
  filter_upwards [hl,hn,hg] with ω hl hn hg hp
  have hp' : (H : WithTop ℝ≥0) ≤ ContinuousNormExit.exit
      (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω := hp.le
  have hlocal := hl hp
  rw [FiniteItoStoppedVersions.stop_horizon] at hlocal
  have hnative := hn hp'
  have hglobal := hg
  change MatrixFourierCoordinates.coordinate i a m
      (MatrixUnboundedContinuousConvolution.physical S H (unitTime H hH H le_rfl) ω) = _
  exact hlocal.trans ((congrArg (fun z : ℝ => Real.exp (-(H : ℝ)*(m : ℝ)^2)*z)
    hnative).trans hglobal.symm)

/-- Before each norm exit, all vector Fourier coordinates agree and
therefore the actual Hilbert vectors coincide. -/
theorem physical_eq (H : ℝ≥0) (hH : 0<H) (N : ℕ) :
    ∀ᵐ ω ∂μc,
      (H : WithTop ℝ≥0) < ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
      MatrixUnboundedContinuousConvolution.physical S H (unitTime H hH H le_rfl) ω =
      MatrixUnboundedCompletedRemainder.value S H ω := by
  have hr := ae_all_iff.mpr (fun i : Fin n =>
    ae_all_iff.mpr (fun m : ℤ => coordinate S H hH N i Complex.reCLM m))
  have hi := ae_all_iff.mpr (fun i : Fin n =>
    ae_all_iff.mpr (fun m : ℤ => coordinate S H hH N i Complex.imCLM m))
  filter_upwards [hr,hi] with ω hr hi hp
  exact MatrixFourierCoordinates.ext (fun i m => hr i m hp)
    (fun i m => hi i m hp)

/-- L2 exit levels exhaust every continuous path, so the constructed
continuous vector heat field is the global Hilbert stochastic remainder. -/
theorem physical_eq_global (H : ℝ≥0) (hH : 0<H) :
    (fun ω => MatrixUnboundedContinuousConvolution.physical S H
      (unitTime H hH H le_rfl) ω) =ᵐ[μc]
      MatrixUnboundedCompletedRemainder.value S H := by
  have hN := ae_all_iff.mpr (fun N : ℕ => physical_eq S H hH N)
  filter_upwards [hN] with ω hω
  have ht := ContinuousNormExit.tendsto_top
    (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω))
    (MatrixUnboundedCompletedLocalField.native_continuous S) ω
  rw [WithTop.tendsto_nhds_top_iff] at ht
  obtain ⟨N, hN⟩ := (ht H).exists
  exact hω N hN

/-- The completed unbounded vector solution has a literal Hilbert-valued
stochastic heat convolution at every prescribed positive time. -/
theorem mild_decomposition (H : ℝ≥0) (hH : 0<H) :
    (fun ω => MatrixUnboundedCompletedGlobal.state S (H,ω)) =ᵐ[μc]
      fun ω => VectorAnalyticHeat.heat (H : ℝ)
        (MatrixGlobalBlockPath.state 1 0 ω.2) +
        MatrixUnboundedContinuousConvolution.physical S H
          (unitTime H hH H le_rfl) ω := by
  filter_upwards [physical_eq_global S H hH] with ω hω
  rw [hω]
  exact MatrixUnboundedCompletedRemainder.decomposition S H ω

/-- The same Fourier comparison works at every prescribed earlier
observation time in one fixed finite Brownian horizon. -/
theorem coordinate_at (H : ℝ≥0) (hH : 0<H) (T : ℝ≥0) (hTH : T≤H)
    (N : ℕ) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ ω ∂μc,
      (T : WithTop ℝ≥0) < ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
      MatrixFourierCoordinates.coordinate i a m
        (MatrixUnboundedContinuousConvolution.physical S H (unitTime H hH T hTH) ω) =
      MatrixFourierCoordinates.coordinate i a m
        (MatrixUnboundedCompletedRemainder.value S T ω) := by
  have hl := MatrixUnboundedLocalFourierConvolution.coordinate S H hH i N T hTH a m
  have hn := MatrixUnboundedCompletedExitIto.native_stopped_integral_eq S H T N i a m
  have hg := MatrixUnboundedCompletedRemainder.fourier_coordinate_at S H T hTH i a m
  filter_upwards [hl,hn,hg] with ω hl hn hg hp
  have hp' : (T : WithTop ℝ≥0) ≤ ContinuousNormExit.exit
      (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω := hp.le
  have hlocal := hl hp
  have hnative := hn hp'
  have hglobal := hg
  change MatrixFourierCoordinates.coordinate i a m
      (MatrixUnboundedContinuousConvolution.physical S H (unitTime H hH T hTH) ω) = _
  exact hlocal.trans ((congrArg (fun z : ℝ => Real.exp (-(T : ℝ)*(m : ℝ)^2)*z)
    hnative).trans hglobal.symm)

theorem physical_eq_global_at (H : ℝ≥0) (hH : 0<H)
    (T : ℝ≥0) (hTH : T≤H) :
    (fun ω => MatrixUnboundedContinuousConvolution.physical S H
      (unitTime H hH T hTH) ω) =ᵐ[μc]
      MatrixUnboundedCompletedRemainder.value S T := by
  have hlocal (N : ℕ) : ∀ᵐ ω ∂μc,
      (T : WithTop ℝ≥0) < ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
      MatrixUnboundedContinuousConvolution.physical S H (unitTime H hH T hTH) ω =
      MatrixUnboundedCompletedRemainder.value S T ω := by
    have hr := ae_all_iff.mpr (fun i : Fin n =>
      ae_all_iff.mpr (fun m : ℤ => coordinate_at S H hH T hTH N i Complex.reCLM m))
    have hi := ae_all_iff.mpr (fun i : Fin n =>
      ae_all_iff.mpr (fun m : ℤ => coordinate_at S H hH T hTH N i Complex.imCLM m))
    filter_upwards [hr,hi] with ω hr hi hp
    exact MatrixFourierCoordinates.ext (fun i m => hr i m hp)
      (fun i m => hi i m hp)
  have hN := ae_all_iff.mpr hlocal
  filter_upwards [hN] with ω hω
  have ht := ContinuousNormExit.tendsto_top
    (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω))
    (MatrixUnboundedCompletedLocalField.native_continuous S) ω
  rw [WithTop.tendsto_nhds_top_iff] at ht
  obtain ⟨N, hN⟩ := (ht T).exists
  exact hω N hN

end SHEStochastic.MatrixUnboundedMildBeforeExit
