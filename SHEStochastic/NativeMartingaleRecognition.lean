module

public import SHEStochastic.MartingaleSimplePairing
public import SHEStochastic.NativeIntegralRecognition
public import SHEStochastic.NativeCrossCompensator
public import SHEStochastic.FiniteItoStoppedVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeMartingaleRecognition
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

/-- The exact terminal second moment follows from the square
compensator and zero initial value. -/
theorem second_moment (r : Process (E := C) F μ H) (M : ℝ≥0 → Ω → ℝ)
    (hM2 : MemLp (M H) 2 μ) (hzero : M 0 =ᵐ[μ] fun _ ↦ (0 : ℝ))
    (hSquare : Martingale (fun t sample ↦ M t sample^2-PredictableBracket.energy r t sample) F μ) :
    (∫ sample, M H sample^2 ∂μ) = ‖r‖^2 := by
  have hs := hSquare.setIntegral_eq (show (0 : ℝ≥0) ≤ H from zero_le) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hs
  have hi : (fun sample ↦ M 0 sample^2-PredictableBracket.energy r 0 sample) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hzero] with sample hz
    simp [hz, PredictableBracket.energy]
  rw [integral_congr_ae hi, integral_zero,
    integral_sub hM2.integrable_sq (PredictableBracket.integrable r H)] at hs
  have he := PredictableBracket.stopped_eq r H
  rw [FiniteItoStoppedVersions.stop_horizon] at he
  have hE : (∫ sample, PredictableBracket.energy r H sample ∂μ) = ‖r‖^2 :=
    (integral_congr_ae he.symm).trans (StochasticExponential.expected_bracket F μ H r)
  linarith

/-- A martingale with the same Brownian cross-compensators as a native
integral, and its exact second moment, IS that native integral. Pairing
of predictable cells and existing cylindrical density supply the proof;
no abstract martingale representation theorem is assumed. -/
theorem integral (r : Process (E := C) F μ H) (M N : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M F μ) (hN : Martingale N F μ)
    (hM2 : ∀ t, t ≤ H → MemLp (M t) 2 μ) (hN2 : ∀ t, t ≤ H → MemLp (N t) 2 μ)
    (A : ι → ℝ≥0 → Ω → ℝ)
    (hCrossM : ∀ i, Martingale (fun t sample ↦ M t sample * P.W i t sample-A i t sample) F μ)
    (hCrossN : ∀ i, Martingale (fun t sample ↦ N t sample * P.W i t sample-A i t sample) F μ)
    (hNative : N H =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral r)
    (hEnergy : (∫ sample, M H sample^2 ∂μ) = ‖r‖^2) :
    M H =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral r := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let m : Lp ℝ 2 μ := (hM2 H le_rfl).toLp (M H)
  let n : Lp ℝ 2 μ := (hN2 H le_rfl).toLp (N H)
  have hm : (m : Ω → ℝ) =ᵐ[μ] M H := (hM2 H le_rfl).coeFn_toLp
  have hn : (n : Ω → ℝ) =ᵐ[μ] N H := (hN2 H le_rfl).coeFn_toLp
  have hnJ : n = (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral r :=
    Lp.ext (hn.trans hNative)
  have hScalar (i : ι) (V : FiniteScalarIto.Simple F H) :
      inner ℝ m (FiniteScalarIto.simpleLp P.toCoordinates i V) =
        inner ℝ n (FiniteScalarIto.simpleLp P.toCoordinates i V) := by
    have hs : (FiniteScalarIto.simpleLp P.toCoordinates i V : Ω → ℝ) =ᵐ[μ]
        FiniteScalarIto.simpleValue P.toCoordinates i V :=
      (FiniteScalarIto.memLp_simpleValue P.toCoordinates i V).coeFn_toLp
    have hl : (fun sample ↦ inner ℝ (m sample) (FiniteScalarIto.simpleLp P.toCoordinates i V sample)) =ᵐ[μ]
        (fun sample ↦ M H sample * FiniteScalarIto.simpleValue P.toCoordinates i V sample) := by
      filter_upwards [hm, hs] with sample hm hs
      rw [hm, hs]
      simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    have hr : (fun sample ↦ inner ℝ (n sample) (FiniteScalarIto.simpleLp P.toCoordinates i V sample)) =ᵐ[μ]
        (fun sample ↦ N H sample * FiniteScalarIto.simpleValue P.toCoordinates i V sample) := by
      filter_upwards [hn, hs] with sample hn hs
      rw [hn, hs]
      simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    rw [L2.inner_def, L2.inner_def, integral_congr_ae hl, integral_congr_ae hr]
    exact MartingaleSimplePairing.pairing P M N hM hN hM2 hN2 i (A i) (hCrossM i) (hCrossN i) V
  have hSimple (s : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
      inner ℝ m (FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.simpleEmbedding e s)) =
        inner ℝ n (FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.simpleEmbedding e s)) := by
    induction s using Finsupp.induction_linear with
    | zero => simp only [map_zero, inner_zero_right]
    | add v w hv hw => rw [map_add, map_add, inner_add_right, inner_add_right, hv, hw]
    | single i V =>
      rw [FiniteCylindricalIto.simpleEmbedding_single, FiniteCylindricalIto.rawIntegral_unit,
        FiniteScalarIto.rawIsometry_simple]
      exact hScalar i V
  have hp (s : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
      inner ℝ m (FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.simpleEmbedding e s)) =
        inner ℝ (FiniteCylindricalIto.processTransport r) (FiniteCylindricalIto.simpleEmbedding e s) := by
    rw [hSimple, hnJ]
    exact (FiniteCylindricalIto.rawIntegral P.toCoordinates e).inner_map_map _ _
  have hE : ‖m‖^2 = ‖r‖^2 := by
    calc
      _ = ∫ sample, M H sample^2 ∂μ := by
        rw [realLp_norm_sq]
        apply integral_congr_ae
        filter_upwards [hm] with sample hm
        rw [hm, Real.norm_eq_abs, sq_abs]
      _ = _ := hEnergy
  have he := NativeIntegralRecognition.integral P e r m hE hp
  rw [he] at hm
  exact hm.symm

/-- The full native integral process is fixed by the unknown
martingale's square and Brownian mixed compensators. Terminal
identification extends to every earlier time by conditional expectation. -/
theorem process (r : Process (E := C) F μ H) (M N : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M F μ) (hN : Martingale N F μ)
    (hM2 : ∀ t, t ≤ H → MemLp (M t) 2 μ) (hN2 : ∀ t, t ≤ H → MemLp (N t) 2 μ)
    (A : ι → ℝ≥0 → Ω → ℝ)
    (hCrossM : ∀ i, Martingale (fun t sample ↦ M t sample * P.W i t sample-A i t sample) F μ)
    (hCrossN : ∀ i, Martingale (fun t sample ↦ N t sample * P.W i t sample-A i t sample) F μ)
    (hNative : ∀ t, t ≤ H → N t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H t r))
    (hzero : M 0 =ᵐ[μ] fun _ ↦ (0 : ℝ))
    (hSquare : Martingale (fun t sample ↦ M t sample^2-PredictableBracket.energy r t sample) F μ) :
    ∀ t, t ≤ H → M t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H t r) := by
  have hNH := hNative H le_rfl
  rw [FiniteItoStoppedVersions.stop_horizon] at hNH
  have hMH := integral P e r M N hM hN hM2 hN2 A hCrossM hCrossN hNH
    (second_moment r M (hM2 H le_rfl) hzero hSquare)
  have hMN : M H =ᵐ[μ] N H := hMH.trans hNH.symm
  intro t ht
  exact (hM.condExp_ae_eq ht).symm.trans
    ((condExp_congr_ae hMN).trans ((hN.condExp_ae_eq ht).trans (hNative t ht)))

end SHEStochastic.NativeMartingaleRecognition
