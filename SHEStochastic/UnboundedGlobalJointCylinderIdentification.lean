module

public import SHEStochastic.UnboundedGlobalFiniteJointClosedVersion
public import SHEStochastic.UnboundedJointCylinderIdentification
public import SHEStochastic.JointFourierNativeGeneratorDensity
public import SHEStochastic.JointFourierCylinderGenerator
public import SHEStochastic.NativeCompensatedItoMartingale
public import SHEStochastic.ContinuousStoppedMartingaleTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.UnboundedGlobalJointCylinderIdentification
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation FourierDiagonalFlow GaussianItoTest FiniteStateDriverCoordinates
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {s d : ℕ} (f : State (s + d) → ℝ) (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2)
  {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (driver : Fin d → ι)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

open UnboundedJointCylinderIdentification

/-- The native unbounded equation gives the full joint cylinder
martingale up to each actual L2 exit, with the original driver retained.
All state/driver cross brackets come from the same native integral. -/
theorem exists_random_martingale (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ) (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ sample, Continuous (M · sample)) ∧ StronglyAdapted F M ∧
      StronglyMeasurable[F.predictable] (Function.uncurry M) ∧ Martingale M F μ ∧
      ∀ T : ℝ≥0, T ≤ H → ∀ᵐ sample ∂μ, (T : WithTop ℝ≥0) ≤ exit W N sample →
        canonical hG hβ hβ1 f a n F μ H W P e driver hf hs T sample = M T sample := by
  obtain ⟨Y, hY, hcY, hYr, hClosed⟩ := UnboundedGlobalFiniteJointClosedVersion.exists_random_version
    F μ H W hW hG hβ hβ1 P e ξ hξ hInitial hH hcW hnull hEquation N a n driver
  let U := UnboundedL2Localization.state (physical W) N
  have hU := UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N
  have hbound := UnboundedL2Localization.history_bound (physical W) μ H N
  let R := NativeStateDriverCoordinates.rows e driver
    (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i))
  let z (sample : Ω) := append (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) (ξ sample))) (0 : State d)
  let nf := frequencies (d := d) n
  let g := FourierDecayItoTest.value f H nf
  let dg := FourierDecayItoTest.derivative f hf hs H nf
  have hreg : RegularTest 0 H g dg := FourierDecayItoTest.regular f hf hs hSmooth H nf
  let u := FiniteItoNoise.gradientProcess F μ H Y hY R g (FiniteItoNoise.regular_admissible hreg)
  obtain ⟨M, hcM, haM, hpM, hmM, hrM⟩ := NativeMartingaleVersion.exists_version P e hnull u
  have hPrim := JointFourierNativeGeneratorDensity.primitive hG hβ hβ1 a n e driver F U hU μ H hbound f hf hs hSmooth Y
  refine ⟨M, hcM, haM, hpM, hmM, ?_⟩
  intro T hT
  have hTH : T ≤ H := hT
  have hComp := NativeCompensatedItoMartingale.represents_random F μ H R Y P e z hY hcY hYr g dg hreg T
  filter_upwards [hClosed, hPrim, hComp, hrM T] with sample hClosed hPrim hComp hrM hBefore
  have hEnd : g T (Y (T, sample)) = f (FiniteStateDriverCoordinates.projection a n driver
      (joint F μ H W P T sample)) := congrArg f (hClosed T hT hBefore)
  have hStart : g 0 (Y (0, sample)) = f (FiniteStateDriverCoordinates.projection a n driver
      (joint F μ H W P 0 sample)) :=
    congrArg f (hClosed 0 zero_le (by exact_mod_cast (show (⊥ : WithTop ℝ≥0) ≤ exit W N sample from bot_le)))
  have hInt : (∫ r in (0 : ℝ)..(T : ℝ), JointFourierNativeGeneratorDensity.density hG hβ hβ1 a n e driver f hf hs
      (U (r.toNNReal, sample)) (clamped H nf r (Y (r.toNNReal, sample)))) =
      ∫ r in (0 : ℝ)..(T : ℝ), JointFourierCylinderGenerator.value hG hβ hβ1.le a n
        (fun j ↦ e (driver j)) driver f hf hs (joint F μ H W P r.toNNReal sample) := by
    apply intervalIntegral.integral_congr_Ioo_of_le T.property
    intro r hr
    let t := r.toNNReal
    have htr : (t : ℝ) = r := Real.coe_toNNReal r hr.1.le
    have htT : t < T := by change (t : ℝ) < T; rw [htr]; exact hr.2
    have htH : t ≤ H := htT.le.trans hT
    have htExit : (t : WithTop ℝ≥0) < exit W N sample :=
      (show (t : WithTop ℝ≥0) < T by exact_mod_cast htT).trans_le hBefore
    have huEq : U (t, sample) = NativePhysicalState.push (W t sample) :=
      UnboundedL2Localization.agrees_before_exit (physical W) (physical_continuous W hcW) N (t, sample) htExit
    have hd : clamped H nf r (Y (t, sample)) = FiniteStateDriverCoordinates.projection a n driver
        (joint F μ H W P t sample) := by
      rw [← htr]
      exact hClosed t htH htExit.le
    change JointFourierNativeGeneratorDensity.density hG hβ hβ1 a n e driver f hf hs (U (t, sample))
      (clamped H nf r (Y (t, sample))) = _
    rw [huEq, hd]
    rfl
  have hNativeInt : (∫ r in (0 : ℝ)..(T : ℝ), dg r (Y (r.toNNReal, sample)) + (1 / 2 : ℝ) *
      GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance F μ H R sample r)
        (GaussianTaylor.hessian (g r) (Y (r.toNNReal, sample)))) =
      ∫ r in (0 : ℝ)..(T : ℝ), JointFourierCylinderGenerator.value hG hβ hβ1.le a n
        (fun j ↦ e (driver j)) driver f hf hs (joint F μ H W P r.toNNReal sample) := by
    convert (hPrim T hTH).trans hInt using 1 <;> rfl
  have hIdentify : NativeCompensatedItoMartingale.compensated F μ H R Y g dg T sample =
      canonical hG hβ hβ1 f a n F μ H W P e driver hf hs T sample := by
    unfold NativeCompensatedItoMartingale.compensated
    rw [min_eq_left hTH]
    rw [min_eq_left (show (T : ℝ) ≤ H from hTH)]
    rw [hEnd, hStart, hNativeInt]
    rfl
  exact hIdentify.symm.trans (hComp.trans hrM.symm)

/-- Deterministic-initial specialization. -/
theorem exists_martingale (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (u₀ : RealL2) (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ sample, Continuous (M · sample)) ∧ StronglyAdapted F M ∧
      StronglyMeasurable[F.predictable] (Function.uncurry M) ∧ Martingale M F μ ∧
      ∀ T : ℝ≥0, T ≤ H → ∀ᵐ sample ∂μ, (T : WithTop ℝ≥0) ≤ exit W N sample →
        canonical hG hβ hβ1 f a n F μ H W P e driver hf hs T sample = M T sample := by
  exact exists_random_martingale hG hβ hβ1 f a n F μ H W P e driver hW (fun _ ↦ u₀) stronglyMeasurable_const
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull
      (UnboundedGlobalNativeEquation.to_local F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hEquation))
    hH hcW hnull hEquation hf hSmooth hs N

theorem stopped_random_martingale (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ) (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    Martingale (stoppedProcess (canonical hG hβ hβ1 f a n F μ H W P e driver hf hs)
      (fun sample ↦ min ((H : ℝ≥0) : WithTop ℝ≥0) (exit W N sample))) F μ := by
  obtain ⟨M, hcM, _, _, hmM, hr⟩ := exists_random_martingale hG hβ hβ1 f a n F μ H W P e driver
    hW ξ hξ hInitial hH hcW hnull hEquation hf hSmooth hs N
  have hzero : canonical hG hβ hβ1 f a n F μ H W P e driver hf hs 0 =ᵐ[μ] M 0 :=
    (hr 0 zero_le).mono fun sample hh ↦ hh
      (by exact_mod_cast (show (⊥ : WithTop ℝ≥0) ≤ exit W N sample from bot_le))
  have he (T : ℝ≥0) (ht : T < H) : ∀ᵐ sample ∂μ,
      (T : WithTop ℝ≥0) < exit W N sample →
        canonical hG hβ hβ1 f a n F μ H W P e driver hf hs T sample = M T sample :=
    (hr T ht.le).mono fun _ hh hb ↦ hh hb.le
  have heq := ContinuousEqualityBeforeExit.stopped_eq_horizon μ
    (canonical hG hβ hβ1 f a n F μ H W P e driver hf hs) M (H) (exit W N)
    (Eventually.of_forall (continuous_canonical hG hβ hβ1 f a n F μ H W P e driver hf hs hcW))
    (Eventually.of_forall hcM) hzero he
  have hτ : IsStoppingTime F (fun sample ↦ min ((H : ℝ≥0) : WithTop ℝ≥0) (exit W N sample)) :=
    (isStoppingTime_const F (H)).min (exit_stopping F W hW hcW N)
  have hm := hmM.stoppedProcess (fun sample t ↦ (hcM sample).continuousAt.continuousWithinAt) hτ
  have ha : StronglyAdapted F (stoppedProcess (canonical hG hβ hβ1 f a n F μ H W P e driver hf hs)
      (fun sample ↦ min ((H : ℝ≥0) : WithTop ℝ≥0) (exit W N sample))) := fun t ↦
    NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t (hm.stronglyAdapted t)
      (heq.mono fun sample hh ↦ hh t)
  exact hm.congr ha (fun t ↦ heq.mono fun sample hh ↦ (hh t).symm)

/-- Deterministic-initial specialization. -/
theorem stopped_martingale (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (u₀ : RealL2) (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    Martingale (stoppedProcess (canonical hG hβ hβ1 f a n F μ H W P e driver hf hs)
      (fun sample ↦ min ((H : ℝ≥0) : WithTop ℝ≥0) (exit W N sample))) F μ := by
  exact stopped_random_martingale hG hβ hβ1 f a n F μ H W P e driver hW (fun _ ↦ u₀) stronglyMeasurable_const
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull
      (UnboundedGlobalNativeEquation.to_local F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hEquation))
    hH hcW hnull hEquation hf hSmooth hs N

end SHEStochastic.UnboundedGlobalJointCylinderIdentification
