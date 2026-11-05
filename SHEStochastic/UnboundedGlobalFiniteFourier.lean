module

public import SHEStochastic.UnboundedGlobalFourierEquation
public import SHEStochastic.UnboundedFiniteFourierClosedVersion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.UnboundedGlobalFiniteFourier
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation FourierDiagonalFlow
open scoped ENNReal NNReal

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T:=2*Real.pi)))) {d : ℕ}

/-- The same finite vector of native stochastic integrals represents
all Fourier coordinates up to the closed L2 exit on the full horizon. -/
theorem exists_random_version (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ)
    (hInitial : W 0=ᵐ[μ] ξ) (hH : 0<H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (N : ℕ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) :
    ∃ Y : ℝ≥0 × Ω → GaussianItoTest.State d,
      StronglyMeasurable[F.predictable] Y ∧ (∀ ω, Continuous (fun t ↦ Y (t,ω))) ∧
      (∀ t : ℝ≥0, (fun ω ↦ Y (t,ω))=ᵐ[μ]
        (fun sample ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
          (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ sample)))
          (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)) t sample)) ∧
      ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, T≤H → (T:WithTop ℝ≥0)≤exit W N ω →
        clamped H n T (Y (T,ω))=FourierCylinderGenerator.projection a n (W T ω) := by
  letI : Fact ((2:ℝ≥0∞)≠∞) := ⟨by norm_num⟩
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T:=2*Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T:=2*Real.pi))) := ⟨rfl⟩
  let R := fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)
  let z (sample : Ω) : GaussianItoTest.State d :=
    WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ sample))
  have hz : StronglyMeasurable[F 0] z := by
    convert (FourierCylinderGenerator.projection a n).continuous.comp_stronglyMeasurable hξ using 1 <;> rfl
  obtain ⟨Y,hp,hc,hr⟩ := NativeFiniteMartingaleVersion.exists_random_version P e hnull R z hz
  let X (t : ℝ≥0) (ω : Ω) := FourierCylinderGenerator.projection a n (W t ω)
  let Z (t : ℝ≥0) (ω : Ω) := clamped H n t (Y (t,ω))
  have hx (ω : Ω) : Continuous (X · ω) := (FourierCylinderGenerator.projection a n).continuous.comp (hcW ω)
  have hzcont (ω : Ω) : Continuous (Z · ω) :=
    ((continuous_clamped H n).comp NNReal.continuous_coe).clm_apply (hc ω)
  have hY0 := NativeFiniteMartingaleVersion.initial_random (FiniteCylindricalIto.terminalIto P.toCoordinates e) R z Y (hr 0)
  have h0 : X 0=ᵐ[μ] Z 0 := by
    filter_upwards [hY0,hInitial] with ω hy hw
    change FourierCylinderGenerator.projection a n (W 0 ω)=clamped H n 0 (Y (0,ω))
    rw [hw,hy]
    have hd := congrArg (fun L : GaussianItoTest.State d →L[ℝ] GaussianItoTest.State d ↦ L (z ω))
      ((clamped_eq n ⟨le_rfl,H.property⟩).trans (raw_zero n))
    convert hd.symm using 1 <;> rfl
  have he (T : ℝ≥0) (hTH : T<H) : ∀ᵐ ω ∂μ,
      (T:WithTop ℝ≥0)<exit W N ω → X T ω=Z T ω := by
    have hi := ae_all_iff.mpr (fun i ↦ UnboundedGlobalFourierEquation.integrating_factor_random
      F μ H hH W hW hG hβ hβ1 P e ξ hcW hEquation N (a i) (n i) T hTH)
    have hlocal : ∀ᵐ ω ∂μ, (T:WithTop ℝ≥0)<exit W N ω →
        Y (T,ω)=WithLp.toLp 2 (fun i ↦ Real.exp ((T:ℝ)*(n i:ℝ)^2)*X T ω i) := by
      filter_upwards [hr T,hi] with ω hy hi hb
      apply PiLp.ext
      intro i
      have hyi := congrArg (fun v : GaussianItoTest.State d ↦ v i) hy
      have hmi := hi i hb
      change Y (T,ω) i=z ω i+(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T (R i)) ω at hyi
      change Y (T,ω) i=_
      rw [hyi]
      change NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ ω)+_=
        Real.exp ((T:ℝ)*(n i:ℝ)^2)*NativeFourierHeatCoordinate.coordinate (a i) (n i) (W T ω)
      change Real.exp ((T:ℝ)*(n i:ℝ)^2)*NativeFourierHeatCoordinate.coordinate (a i) (n i) (W T ω)-
        NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ ω)=
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H T (R i)) ω at hmi
      linarith
    filter_upwards [hlocal] with ω hy hb
    change X T ω=clamped H n T (Y (T,ω))
    rw [hy hb]
    have hd := congrArg (fun L : GaussianItoTest.State d →L[ℝ] GaussianItoTest.State d ↦
      L (WithLp.toLp 2 (fun i ↦ Real.exp ((T:ℝ)*(n i:ℝ)^2)*X T ω i)))
      (clamped_eq n ⟨T.property,hTH.le⟩)
    convert (hd.trans (raw_inverse_scaled n T (X T ω))).symm using 1 <;> rfl
  refine ⟨Y,hp,hc,hr,?_⟩
  exact (ContinuousEqualityBeforeExit.simultaneous_horizon μ X Z H (exit W N)
    (Eventually.of_forall hx) (Eventually.of_forall hzcont) h0 he).mono fun ω hh T ht hb ↦ (hh T ht hb).symm

end SHEStochastic.UnboundedGlobalFiniteFourier
