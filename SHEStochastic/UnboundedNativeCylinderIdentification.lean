module

public import SHEStochastic.UnboundedFiniteFourierClosedVersion
public import SHEStochastic.FourierNativeGeneratorDensity
public import SHEStochastic.NativeCompensatedItoMartingale
public import SHEStochastic.ContinuousStoppedMartingaleTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedNativeCylinderIdentification
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation FourierDiagonalFlow GaussianItoTest
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {d : ℕ} (f : State d → ℝ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ)

def canonical (W : ℝ≥0 → Ω → RealL2) (u₀ : RealL2) (T : ℝ≥0) (sample : Ω) : ℝ :=
  f (FourierCylinderGenerator.projection a n (W T sample)) - f (FourierCylinderGenerator.projection a n u₀) -
    ∫ r in (0 : ℝ)..(T : ℝ), FourierCylinderGenerator.value f hG hβ hβ1.le a n (W r.toNNReal sample)

theorem continuous_canonical (hf : ContDiff ℝ 2 f) (W : ℝ≥0 → Ω → RealL2)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) (u₀ : RealL2) (sample : Ω) :
    Continuous (fun T ↦ canonical hG hβ hβ1 f a n W u₀ T sample) := by
  have hb := FourierCylinderGenerator.continuous_value f hf hG hβ hβ1.le a n
  have hi : Continuous (fun T : ℝ≥0 ↦ ∫ r in (0 : ℝ)..(T : ℝ),
      FourierCylinderGenerator.value f hG hβ hβ1.le a n (W r.toNNReal sample)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
    · exact hb.comp ((hcW sample).comp (continuous_real_toNNReal.comp continuous_snd))
    · exact NNReal.continuous_coe
  exact ((hf.continuous.comp ((FourierCylinderGenerator.projection a n).continuous.comp (hcW sample))).sub
    continuous_const).sub hi

theorem native_density (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (u : RealL2) :
    FourierNativeGeneratorDensity.density hG hβ hβ1 a n f hf hs
      (NativePhysicalState.push u) (FourierCylinderGenerator.projection a n u) =
        FourierCylinderGenerator.value f hG hβ hβ1.le a n u := by
  rw [FourierNativeGeneratorDensity.density, FourierCylinderGenerator.heatDrift_apply]
  rfl

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)

/-- Shared native finite-Itô identification. The supplied Fourier
version may cover any closed subinterval of the native horizon; the
stochastic calculus and generator calculation are independent of its length. -/
theorem exists_martingale_of_closed (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (N : ℕ) (K : ℝ≥0) (hK : K≤H)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (Y : ℝ≥0 × Ω → State d) (hY : StronglyMeasurable[F.predictable] Y)
    (hcY : ∀ sample, Continuous (fun t ↦ Y (t,sample)))
    (hYr : ∀ t : ℝ≥0, (fun sample ↦ Y (t,sample))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
        (WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) u₀))
        (fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)) t)
    (hClosed : ∀ᵐ sample ∂μ, ∀ T : ℝ≥0, T≤K → (T:WithTop ℝ≥0)≤exit W N sample →
      clamped H n T (Y (T,sample))=FourierCylinderGenerator.projection a n (W T sample))
    (hinitial : W 0=ᵐ[μ] fun _ ↦ u₀) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ sample, Continuous (M · sample)) ∧ StronglyAdapted F M ∧
      StronglyMeasurable[F.predictable] (Function.uncurry M) ∧ Martingale M F μ ∧
      ∀ T : ℝ≥0, T≤K → ∀ᵐ sample ∂μ, (T:WithTop ℝ≥0)≤exit W N sample →
        canonical hG hβ hβ1 f a n W u₀ T sample=M T sample := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  let U := UnboundedL2Localization.state (physical W) N
  have hU := UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N
  have hbound := UnboundedL2Localization.history_bound (physical W) μ H N
  let R := fun i ↦ UnboundedNativeFourierEquation.growingInput F μ H W hW hG hβ hβ1 N (a i) (n i)
  let z : State d := WithLp.toLp 2 (fun i ↦ NativeFourierHeatCoordinate.coordinate (a i) (n i) u₀)
  let g := FourierDecayItoTest.value f H n
  let dg := FourierDecayItoTest.derivative f hf hs H n
  have hreg : RegularTest 0 H g dg := FourierDecayItoTest.regular f hf hs hSmooth H n
  let u := FiniteItoNoise.gradientProcess F μ H Y hY R g (FiniteItoNoise.regular_admissible hreg)
  obtain ⟨M, hcM, haM, hpM, hmM, hrM⟩ := NativeMartingaleVersion.exists_version P e hnull u
  have hPrim := FourierNativeGeneratorDensity.primitive F U hU hG hβ hβ1 μ H hbound a n f hf hs hSmooth Y
  refine ⟨M, hcM, haM, hpM, hmM, ?_⟩
  intro T hT
  have hTH : T ≤ H := hT.trans hK
  have hComp := NativeCompensatedItoMartingale.represents F μ H R Y P e z hY hcY
    (fun t _ ↦ hYr t) g dg hreg T
  filter_upwards [hClosed, hPrim, hComp, hrM T,
    hinitial]
      with sample hClosed hPrim hComp hrM hw0 hBefore
  have hEnd : g T (Y (T, sample)) = f (FourierCylinderGenerator.projection a n (W T sample)) :=
    congrArg f (hClosed T hT hBefore)
  have hStart : g 0 (Y (0, sample)) = f (FourierCylinderGenerator.projection a n u₀) := by
    have hh := congrArg f (hClosed 0 zero_le (by exact_mod_cast (show (⊥ : WithTop ℝ≥0) ≤ exit W N sample from bot_le)))
    change g 0 (Y (0, sample)) = f (FourierCylinderGenerator.projection a n (W 0 sample)) at hh
    exact hh.trans (congrArg (fun v ↦ f (FourierCylinderGenerator.projection a n v)) hw0)
  have hInt : (∫ r in (0 : ℝ)..(T : ℝ), FourierNativeGeneratorDensity.density hG hβ hβ1 a n f hf hs
      (U (r.toNNReal, sample)) (clamped H n r (Y (r.toNNReal, sample)))) =
      ∫ r in (0 : ℝ)..(T : ℝ), FourierCylinderGenerator.value f hG hβ hβ1.le a n (W r.toNNReal sample) := by
    apply intervalIntegral.integral_congr_Ioo_of_le T.property
    intro r hr
    let s := r.toNNReal
    have hsr : (s : ℝ) = r := Real.coe_toNNReal r hr.1.le
    have hst : s < T := by change (s : ℝ) < T; rw [hsr]; exact hr.2
    have hsH : s ≤ K := hst.le.trans hT
    have hsExit : (s : WithTop ℝ≥0) < exit W N sample :=
      (show (s : WithTop ℝ≥0) < T by exact_mod_cast hst).trans_le hBefore
    have huEq : U (s, sample) = NativePhysicalState.push (W s sample) :=
      UnboundedL2Localization.agrees_before_exit (physical W) (physical_continuous W hcW) N (s, sample) hsExit
    have hd : clamped H n r (Y (s, sample)) = FourierCylinderGenerator.projection a n (W s sample) := by
      rw [← hsr]
      exact hClosed s hsH hsExit.le
    change FourierNativeGeneratorDensity.density hG hβ hβ1 a n f hf hs (U (s, sample))
      (clamped H n r (Y (s, sample))) = _
    rw [huEq, hd]
    exact native_density hG hβ hβ1 f a n hf hs (W s sample)
  have hNativeInt : (∫ r in (0 : ℝ)..(T : ℝ), dg r (Y (r.toNNReal, sample)) + (1 / 2 : ℝ) *
      GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance F μ H R sample r)
        (GaussianTaylor.hessian (g r) (Y (r.toNNReal, sample)))) =
      ∫ r in (0 : ℝ)..(T : ℝ), FourierCylinderGenerator.value f hG hβ hβ1.le a n (W r.toNNReal sample) := by
    have hh := (hPrim T hTH).trans hInt
    convert hh using 1 <;> rfl
  have hIdentify : NativeCompensatedItoMartingale.compensated F μ H R Y g dg T sample =
      canonical hG hβ hβ1 f a n W u₀ T sample := by
    unfold NativeCompensatedItoMartingale.compensated
    rw [min_eq_left hTH]
    rw [min_eq_left (show (T : ℝ) ≤ H from hTH)]
    unfold canonical
    linarith
  exact hIdentify.symm.trans (hComp.trans hrM.symm)


/-- The actual original canonical cylinder expression agrees up to each
closed L2 exit with a genuine continuous native martingale. This derives
the canonical martingale input from the native SPDE formulation. -/
theorem exists_martingale (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ sample, Continuous (M · sample)) ∧ StronglyAdapted F M ∧
      StronglyMeasurable[F.predictable] (Function.uncurry M) ∧ Martingale M F μ ∧
      ∀ T : ℝ≥0, T ≤ min H 1 → ∀ᵐ sample ∂μ, (T : WithTop ℝ≥0) ≤ exit W N sample →
        canonical hG hβ hβ1 f a n W u₀ T sample = M T sample := by
  obtain ⟨Y,hY,hcY,hYr,hClosed⟩ := UnboundedFiniteFourierClosedVersion.exists_version
    F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation N a n
  exact exists_martingale_of_closed hG hβ hβ1 f a n F μ H W hW P e u₀ hcW hnull N (min H 1)
    (min_le_left _ _) hf hSmooth hs Y hY hcY hYr hClosed
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation)

/-- Every compact smooth canonical Fourier cylinder expression of the
original unbounded native solution is a genuine martingale after the
actual L2 exit and closed initial horizon. -/
theorem stopped_martingale (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    Martingale (stoppedProcess (canonical hG hβ hβ1 f a n W u₀)
      (fun sample ↦ min ((min H 1 : ℝ≥0) : WithTop ℝ≥0) (exit W N sample))) F μ := by
  obtain ⟨M, hcM, _, _, hmM, hr⟩ := exists_martingale hG hβ hβ1 f a n F μ H W hW P e u₀
    hH hcW hnull hEquation hf hSmooth hs N
  have hzero : canonical hG hβ hβ1 f a n W u₀ 0 =ᵐ[μ] M 0 :=
    (hr 0 zero_le).mono fun sample hh ↦ hh
      (by exact_mod_cast (show (⊥ : WithTop ℝ≥0) ≤ exit W N sample from bot_le))
  have he (T : ℝ≥0) (ht : T < min H 1) : ∀ᵐ sample ∂μ,
      (T : WithTop ℝ≥0) < exit W N sample → canonical hG hβ hβ1 f a n W u₀ T sample = M T sample :=
    (hr T ht.le).mono fun _ hh hb ↦ hh hb.le
  have heq := ContinuousEqualityBeforeExit.stopped_eq_horizon μ
    (canonical hG hβ hβ1 f a n W u₀) M (min H 1) (exit W N)
    (Eventually.of_forall (continuous_canonical hG hβ hβ1 f a n hf W hcW u₀))
    (Eventually.of_forall hcM) hzero he
  have hτ : IsStoppingTime F (fun sample ↦ min ((min H 1 : ℝ≥0) : WithTop ℝ≥0) (exit W N sample)) :=
    (isStoppingTime_const F (min H 1)).min (exit_stopping F W hW hcW N)
  have hm := hmM.stoppedProcess (fun sample t ↦ (hcM sample).continuousAt.continuousWithinAt) hτ
  have ha : StronglyAdapted F (stoppedProcess (canonical hG hβ hβ1 f a n W u₀)
      (fun sample ↦ min ((min H 1 : ℝ≥0) : WithTop ℝ≥0) (exit W N sample))) := fun t ↦
    NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t (hm.stronglyAdapted t)
      (heq.mono fun sample hh ↦ hh t)
  exact hm.congr ha (fun t ↦ heq.mono fun sample hh ↦ (hh t).symm)

end SHEStochastic.UnboundedNativeCylinderIdentification
