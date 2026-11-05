module

public import SHEStochastic.UnboundedNativeFourierEquation
public import SHEStochastic.NativeFiniteMartingaleVersion
public import SHEStochastic.FourierNoiseCovariance
public import SHEStochastic.FourierCylinderGenerator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.UnboundedNativeFiniteFourier
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation
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

/-- Every finite family of actual Fourier modes has one continuous
predictable native-integral version, agreeing with the integrating
factors of W before each L2 exit. The proved universal finite Ito formula
applies to this very vector and its original covariance rows. -/
theorem exists_random_version (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (N : ℕ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) :
    ∃ Y : ℝ≥0 × Ω → GaussianItoTest.State d,
      StronglyMeasurable[F.predictable] Y ∧ (∀ ω, Continuous (fun t ↦ Y (t, ω))) ∧
      (∀ t : ℝ≥0, (fun ω ↦ Y (t, ω)) =ᵐ[μ]
        (fun sample ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
          (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ sample)))
          (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)) t sample)) ∧
      ∀ (T : ℝ≥0), T < H → (T : ℝ) < 1 →
        ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
          Y (T, ω) = WithLp.toLp 2 (fun i ↦ Real.exp ((T : ℝ) * (n i : ℝ) ^ 2) *
            NativeFourierHeatCoordinate.coordinate (a i) (n i) (W T ω)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  let R := fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)
  let z (sample : Ω) : GaussianItoTest.State d := WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ sample))
  have hz : StronglyMeasurable[F 0] z := by
    convert (FourierCylinderGenerator.projection a n).continuous.comp_stronglyMeasurable hξ using 1 <;> rfl
  obtain ⟨Y, hp, hc, hr⟩ := NativeFiniteMartingaleVersion.exists_random_version P e hnull R z hz
  refine ⟨Y, hp, hc, hr, ?_⟩
  intro T hTH hT
  have hi := ae_all_iff.mpr (fun i ↦ UnboundedNativeFourierEquation.integrating_factor_random F μ H W hW hG hβ hβ1
    P e ξ hcW hEquation N (a i) (n i) T hTH hT)
  filter_upwards [hr T, hi] with ω hr hi hBefore
  apply PiLp.ext
  intro i
  have hy := congrArg (fun v : GaussianItoTest.State d ↦ v i) hr
  have hm := hi i hBefore
  change Y (T, ω) i = z ω i +
    (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H T (R i)) ω at hy
  change Y (T, ω) i = _
  rw [hy]
  change NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ ω) + _ = _
  linarith

/-- Deterministic-initial specialization. -/
theorem exists_version (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (N : ℕ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) :
    ∃ Y : ℝ≥0 × Ω → GaussianItoTest.State d,
      StronglyMeasurable[F.predictable] Y ∧ (∀ ω, Continuous (fun t ↦ Y (t, ω))) ∧
      (∀ t : ℝ≥0, (fun ω ↦ Y (t, ω)) =ᵐ[μ]
        StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
          (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) u₀))
          (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)) t) ∧
      ∀ (T : ℝ≥0), T < H → (T : ℝ) < 1 →
        ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
          Y (T, ω) = WithLp.toLp 2 (fun i ↦ Real.exp ((T : ℝ) * (n i : ℝ) ^ 2) *
            NativeFourierHeatCoordinate.coordinate (a i) (n i) (W T ω)) := by
  exact exists_random_version F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) stronglyMeasurable_const
    hcW hnull hEquation N a n

end SHEStochastic.UnboundedNativeFiniteFourier
