module

public import SHEStochastic.UnboundedFiniteFourierClosedVersion
public import SHEStochastic.NativeStateDriverCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.UnboundedFiniteJointClosedVersion
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation FourierDiagonalFlow GaussianItoTest FiniteStateDriverCoordinates
open scoped ENNReal NNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  {s d : ℕ}

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

/-- Appending finitely many actual Brownian coordinates to the existing
state vector preserves native Itô representation and closed-exit
agreement. The original Fourier construction is reused unchanged. -/
theorem exists_random_version (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ)
    (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (N : ℕ) (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ) (driver : Fin d → ι) :
    ∃ Y : ℝ≥0 × Ω → State (s + d), StronglyMeasurable[F.predictable] Y ∧
      (∀ sample, Continuous (fun t ↦ Y (t, sample))) ∧
      (∀ t : ℝ≥0, t ≤ H → (fun sample ↦ Y (t, sample)) =ᵐ[μ]
        (fun sample ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
          (append (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ sample))) (0 : State d))
          (NativeStateDriverCoordinates.rows e driver
            (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i))) t sample)) ∧
      ∀ᵐ sample ∂μ, ∀ T : ℝ≥0, T ≤ min H 1 → (T : WithTop ℝ≥0) ≤ exit W N sample →
        clamped H (frequencies (d := d) n) T (Y (T, sample)) =
          FiniteStateDriverCoordinates.projection a n driver
            (W T sample, fun i ↦ P.W i T sample - P.W i 0 sample) := by
  obtain ⟨Y, hp, hc, hr, hclosed⟩ := UnboundedFiniteFourierClosedVersion.exists_random_version
    F μ H W hW hG hβ hβ1 P e ξ hξ hInitial hH hcW hnull hEquation N a n
  refine ⟨NativeStateDriverCoordinates.augmented P driver Y,
    NativeStateDriverCoordinates.predictable_augmented P driver Y hp,
    NativeStateDriverCoordinates.continuous_augmented P driver Y hc, ?_, ?_⟩
  · intro t ht
    exact NativeStateDriverCoordinates.represents_random P e driver _ _ Y t ht (hr t)
  · filter_upwards [hclosed] with sample hclosed T hT hBefore
    change clamped H (frequencies (d := d) n) T
      (append (Y (T, sample)) (NativeStateDriverCoordinates.driverVector P driver T sample)) = _
    rw [clamped_append, hclosed T hT hBefore]
    rfl

/-- Deterministic-initial specialization. -/
theorem exists_version (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (N : ℕ) (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ) (driver : Fin d → ι) :
    ∃ Y : ℝ≥0 × Ω → State (s + d), StronglyMeasurable[F.predictable] Y ∧
      (∀ sample, Continuous (fun t ↦ Y (t, sample))) ∧
      (∀ t : ℝ≥0, t ≤ H → (fun sample ↦ Y (t, sample)) =ᵐ[μ]
        StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
          (append (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) u₀)) (0 : State d))
          (NativeStateDriverCoordinates.rows e driver
            (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i))) t) ∧
      ∀ᵐ sample ∂μ, ∀ T : ℝ≥0, T ≤ min H 1 → (T : WithTop ℝ≥0) ≤ exit W N sample →
        clamped H (frequencies (d := d) n) T (Y (T, sample)) =
          FiniteStateDriverCoordinates.projection a n driver
            (W T sample, fun i ↦ P.W i T sample - P.W i 0 sample) := by
  exact exists_random_version F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) stronglyMeasurable_const
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation)
    hH hcW hnull hEquation N a n driver

end SHEStochastic.UnboundedFiniteJointClosedVersion
