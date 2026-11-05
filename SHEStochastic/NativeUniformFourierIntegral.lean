module

public import SHEStochastic.NativeFourierCutoffLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.NativeUniformFourierIntegral
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation UnboundedNativeUniformRegularity StoppedPathPasting
open UnboundedJointCanonicalPathMartingale PastedLinearHeatFunctional NativeContinuationFourierInput
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)



local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩


include hH hnull hEquation hM hu₀ in
/-- The original Fourier mode, stopped at its actual uniform exit, is
the stopped version of the native bounded-cutoff Fourier integral.
This supplies its square and mixed characteristics using the existing
integral theorems, with no new stochastic hypothesis. -/
theorem exists_version (R : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ∃ N : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (N · ω)) ∧ StronglyAdapted F N ∧
      StronglyMeasurable[F.predictable] (Function.uncurry N) ∧ Martingale N F μ ∧
      (∀ T, N T =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T (BoundedFourierInput.input F μ H W hW
          (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
          (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
          (UnboundedCoefficientCutoff.bounded hG R) a n))) ∧
      ∀ᵐ ω ∂μ, ∀ T, stoppedProcess (NativeUniformStoppedFourier.coordinate W a n)
        (fun ω ↦ (AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R ω) : WithTop ℝ≥0)) T ω =
        stoppedProcess N
        (fun ω ↦ (AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R ω) : WithTop ℝ≥0)) T ω := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  let r := BoundedFourierInput.input F μ H W hW (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
    (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hG R) a n
  obtain ⟨N, hcN, haN, hpN, hmN, hrN⟩ := NativeMartingaleVersion.exists_version P e hnull r
  refine ⟨N, hcN, haN, hpN, hmN, hrN, ?_⟩
  let τ := fun ω ↦ AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R ω)
  let O := NativeUniformStoppedFourier.coordinate W a n
  have hInitial := UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation
  have hfixed (T : ℝ≥0) (hTH : T < H) (hT : (T : ℝ) < 1) :
      ∀ᵐ ω ∂μ, T < τ ω → O T ω = N T ω := by
    have hN (j : ℕ) : ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W j ω → T < τ ω → O T ω = N T ω := by
      filter_upwards [UnboundedNativeFourierEquation.integrating_factor F μ H W hW hG hβ hβ1
        P e u₀ hcW hEquation j a n T hTH hT,
        NativeFourierCutoffLocality.integral_agrees F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation
          M hM hu₀ R j a n T, hrN T, hInitial] with ω he hi hr hz hBefore hUniform
      change NativeUniformStoppedFourier.coordinate W a n T ω = _
      rw [NativeUniformStoppedFourier.coordinate, hz]
      exact (he hBefore).trans ((hi (le_min hBefore.le (WithTop.coe_le_coe.mpr hUniform.le))).trans hr.symm)
    filter_upwards [ae_all_iff.mpr hN] with ω hω ht
    have hEsc := ContinuousNormExit.tendsto_top (fun t ω ↦ physical W (t,ω)) (physical_continuous W hcW) ω
    rw [WithTop.tendsto_nhds_top_iff] at hEsc
    obtain ⟨j, hj⟩ := (hEsc T).exists
    exact hω j hj ht
  have hzero : O 0 =ᵐ[μ] N 0 := by
    have hh := hrN 0
    rw [NNReal.coe_zero, StoppedItoInputs.stop_zero, map_zero] at hh
    filter_upwards [hh, Lp.coeFn_zero ℝ 2 μ] with ω hn hz
    simp only [O, NativeUniformStoppedFourier.coordinate, NNReal.coe_zero, zero_mul, Real.exp_zero,
      one_mul, sub_self]
    exact (hn.trans hz).symm
  have hcO (ω : Ω) : Continuous (fun T ↦ O T ω) := by
    unfold O NativeUniformStoppedFourier.coordinate
    fun_prop
  apply ContinuousEqualityBeforeExit.stopped_eq μ O N τ (Filter.Eventually.of_forall hcO)
    (Filter.Eventually.of_forall hcN) hzero
  intro T
  by_cases hTH : T < H
  · by_cases hT : (T : ℝ) < 1
    · exact hfixed T hTH hT
    · exact Filter.Eventually.of_forall fun ω ht ↦
        (hT (show (T : ℝ) < 1 from ht.trans_le (uniformExit H W hcW R ω).property.2 |>.trans_le (min_le_right _ _))).elim
  · exact Filter.Eventually.of_forall fun ω ht ↦
      (hTH (ht.trans_le (uniformExit H W hcW R ω).property.2 |>.trans_le (min_le_left _ _))).elim

end SHEStochastic.NativeUniformFourierIntegral
