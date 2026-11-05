module

public import SHEStochastic.UnboundedNativeFiniteFourier
public import SHEStochastic.UnboundedNativeMildRecognition
public import SHEStochastic.FourierDiagonalFlow
public import SHEStochastic.ContinuousEqualityBeforeExit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedFiniteFourierClosedVersion
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation FourierDiagonalFlow
open scoped ENNReal NNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  {d : ℕ}

/-- Native finite Ito applies to a vector whose decayed path agrees
simultaneously with the original Fourier projection up to the CLOSED
L2 exit and closed initial horizon. Zero exits are covered by the
proved initial equality. -/
theorem exists_random_version (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ)
    (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (N : ℕ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) :
    ∃ Y : ℝ≥0 × Ω → GaussianItoTest.State d,
      StronglyMeasurable[F.predictable] Y ∧ (∀ ω, Continuous (fun t ↦ Y (t, ω))) ∧
      (∀ t : ℝ≥0, (fun ω ↦ Y (t, ω)) =ᵐ[μ]
        (fun sample ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
          (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ sample)))
          (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)) t sample)) ∧
      ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, T ≤ min H 1 → (T : WithTop ℝ≥0) ≤ exit W N ω →
        clamped H n T (Y (T, ω)) = FourierCylinderGenerator.projection a n (W T ω) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  obtain ⟨Y, hp, hc, hr, hlocal⟩ := UnboundedNativeFiniteFourier.exists_random_version
    F μ H W hW hG hβ hβ1 P e ξ hξ hcW hnull hEquation N a n
  let X (t : ℝ≥0) (ω : Ω) := FourierCylinderGenerator.projection a n (W t ω)
  let Z (t : ℝ≥0) (ω : Ω) := clamped H n t (Y (t, ω))
  have hx (ω : Ω) : Continuous (X · ω) := (FourierCylinderGenerator.projection a n).continuous.comp (hcW ω)
  have hz (ω : Ω) : Continuous (Z · ω) :=
    ((continuous_clamped H n).comp NNReal.continuous_coe).clm_apply (hc ω)
  have hY0 := NativeFiniteMartingaleVersion.initial_random (FiniteCylindricalIto.terminalIto P.toCoordinates e)
    (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i))
    (fun sample ↦ WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ sample))) Y (hr 0)
  have h0 : X 0 =ᵐ[μ] Z 0 := by
    filter_upwards [hY0, hInitial]
      with ω hy hw
    change FourierCylinderGenerator.projection a n (W 0 ω) = clamped H n 0 (Y (0, ω))
    rw [hw, hy]
    have hd := congrArg (fun L : GaussianItoTest.State d →L[ℝ] GaussianItoTest.State d ↦
      L (FourierCylinderGenerator.projection a n (ξ ω)))
      ((clamped_eq n ⟨le_rfl, H.property⟩).trans (raw_zero n))
    convert hd.symm using 1 <;> rfl
  have he (T : ℝ≥0) (hT : T < min H 1) : ∀ᵐ ω ∂μ,
      (T : WithTop ℝ≥0) < exit W N ω → X T ω = Z T ω := by
    have hTH : T < H := hT.trans_le (min_le_left _ _)
    have hT1 : (T : ℝ) < 1 := hT.trans_le (min_le_right _ _)
    filter_upwards [hlocal T hTH hT1] with ω hy hBefore
    change FourierCylinderGenerator.projection a n (W T ω) = clamped H n T (Y (T, ω))
    rw [hy hBefore]
    let z := FourierCylinderGenerator.projection a n (W T ω)
    have hd := congrArg (fun L : GaussianItoTest.State d →L[ℝ] GaussianItoTest.State d ↦
      L (WithLp.toLp 2 (fun i ↦ Real.exp ((T : ℝ) * (n i : ℝ) ^ 2) * z i)))
      (clamped_eq n ⟨T.property, hTH.le⟩)
    convert (hd.trans (raw_inverse_scaled n T z)).symm using 1 <;> rfl
  refine ⟨Y, hp, hc, hr, ?_⟩
  exact (ContinuousEqualityBeforeExit.simultaneous_horizon μ X Z (min H 1) (exit W N)
    (Eventually.of_forall hx) (Eventually.of_forall hz) h0 he).mono fun ω hω T hT hBefore ↦ (hω T hT hBefore).symm

/-- Deterministic-initial specialization, with initial equality derived from the native equation. -/
theorem exists_version (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (N : ℕ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) :
    ∃ Y : ℝ≥0 × Ω → GaussianItoTest.State d,
      StronglyMeasurable[F.predictable] Y ∧ (∀ ω, Continuous (fun t ↦ Y (t, ω))) ∧
      (∀ t : ℝ≥0, (fun ω ↦ Y (t, ω)) =ᵐ[μ]
        StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
          (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) u₀))
          (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)) t) ∧
      ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, T ≤ min H 1 → (T : WithTop ℝ≥0) ≤ exit W N ω →
        clamped H n T (Y (T, ω)) = FourierCylinderGenerator.projection a n (W T ω) := by
  exact exists_random_version F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) stronglyMeasurable_const
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation)
    hH hcW hnull hEquation N a n

end SHEStochastic.UnboundedFiniteFourierClosedVersion
