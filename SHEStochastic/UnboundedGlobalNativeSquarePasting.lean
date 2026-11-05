module

public import SHEStochastic.UnboundedGlobalNativeFourierPasting
public import SHEStochastic.GlobalNativeUniformFourierSquare
public import SHEStochastic.NativeContinuationProductInput
public import SHEStochastic.PastedHeatProductIntegrability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalNativeSquarePasting
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation UnboundedGlobalUniformRegularity StoppedPathPasting
open UnboundedGlobalJointCanonicalPathMartingale PastedLinearHeatFunctional NativeContinuationFourierInput
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
  (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)




include hH hnull hEquation hM hu₀ in
/-- The square characteristic holds on the actual pasted law. Its
integrability follows from the proved source bound and conditional
fourth moments, and both cross terms at the random join are included. -/
theorem law_identity (R : ℕ) (hR : M ≤ R)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)))
    (hLaw : CanonicalInitialKernel.initialLaw (H) Q.toMeasure =
      UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput (H) Q.toMeasure)
    (hFuture : ∀ᵐ u ∂CanonicalInitialKernel.initialLaw (H) Q.toMeasure,
      CanonicalMildFourierCharacteristics.Holds (H)
        (CanonicalInitialKernel.kernel (H) Q.toMeasure u)
        (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
        (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
        (UnboundedCoefficientCutoff.bounded hG R) e)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    PastedHeatProductMartingale.Identity (H) (row (ι := ι) a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2)
      (by positivity) (NativeUniformFourierSquare.density (ι := ι) hG hβ hβ1 R a n)
      (StoppedContinuationMeasure.law (H) (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
        μ (NativeContinuationKernel.joint (H) Q.toMeasure)) := by
  let K := H
  let X := path F μ H W P hcW
  let exit := uniformExit H W hcW R
  let hX := measurable_path F μ H W hW P hcW
  let hr := UnboundedGlobalContinuation.exit_measurable F H W hW hcW R
  let κ := NativeContinuationKernel.joint K Q.toMeasure
  let Z := StoppedContinuationMeasure.state K X exit
  let ν := StoppedContinuationMeasure.joint K X exit hX hr μ κ
  let B := UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R
  let b := NativeUniformFourierSquare.density (ι := ι) hG hβ hβ1 R a n
  have hZ : Measurable Z := StoppedContinuationMeasure.measurable_state K X exit hX hr
  have hp : MeasurePreserving (fun ω ↦ (Z ω).1) μ (CanonicalInitialKernel.initialLaw K Q.toMeasure) := by
    refine ⟨measurable_fst.comp hZ, ?_⟩
    rw [hLaw]
    rfl
  have hi : ∀ᵐ ω ∂μ, ∀ᵐ y ∂κ (Z ω), y (origin K) = Z ω := by
    filter_upwards [hp.quasiMeasurePreserving.ae
      (NativeContinuationCharacteristics.matching_initial K Q.toMeasure hBrown)] with ω hω
    exact hω (Z ω).2
  have hf := (hp.quasiMeasurePreserving.ae
    (NativeContinuationFourierInput.properties K Q.toMeasure (UnboundedCoefficientCutoff.holder hG R)
      hβ hβ1 B (UnboundedCoefficientCutoff.bounded hG R) e hFuture)).mono fun ω hω ↦ hω (Z ω).2 a n
  have hprod := (hp.quasiMeasurePreserving.ae
    (NativeContinuationProductInput.properties K Q.toMeasure (UnboundedCoefficientCutoff.holder hG R)
      hβ hβ1 B (UnboundedCoefficientCutoff.bounded hG R) e hBrown hFuture)).mono fun ω hω ↦ (hω (Z ω).2 a n).1
  have hEnv : MemLp (fun z : Ω × Path K (JointStateDriverPath.State RealL2 ι) ↦
      envelope K (row a n) ((n : ℝ)^2) z.2) 4 ν :=
    PastedLinearHeatIntegrability.future_envelope_memLp K (row a n) ((n : ℝ)^2) μ X exit hX hr κ
      (fourthConstant K B a n) (fourthConstant_lt_top K B a n) (hf.mono fun _ h ↦ h.2)
  let D := Real.exp ((n : ℝ)^2*(K : ℝ))*‖NativeFourierHeatCoordinate.coordinate a n‖*R+
    ‖NativeFourierHeatCoordinate.coordinate a n‖*R
  have hD : ∀ᵐ ω ∂μ, ∀ t : Time K, t ≤ exit ω → ‖value K (row a n) ((n : ℝ)^2) (X ω) t‖ ≤ D :=
    GlobalNativeUniformFourierPrefix.bound F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R hR a n
  intro s t hst test htest
  obtain ⟨hipre, hi0, hi1, hi2⟩ := PastedHeatProductIntegrability.parts K μ X exit hX hr κ
    (row a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2) (sq_nonneg _) (sq_nonneg _) b
    (fun _ ↦ D) (fun _ ↦ D) (memLp_const D) (memLp_const D) hD hD hEnv hEnv s t test
  have hjoint := PastedHeatProductMartingale.joint_identity K (row a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2)
    (by positivity) b X exit hX hr μ κ hi hprod (hf.mono fun _ h ↦ ⟨h.1,h.1⟩)
    s t hst test htest hipre hi0 hi1 hi2
    (PastedHeatProductMartingale.stopped_source_identity K (row a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2)
      (by positivity) b X exit μ F (adapted_path F μ H W hW P hcW)
      (GlobalNativeUniformFourierSquare.martingale F μ H W hW hG hβ hβ1 P e u₀
        hH hcW hnull hEquation M hM hu₀ R a n) s t hst test htest)
  have hv (q : Time K) : Continuous (fun y : Path K (JointStateDriverPath.State RealL2 ι) ↦
      PastedHeatProductFunctional.value K (row a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2) (by positivity) b y q) :=
    (PastedHeatProductFunctional.continuous_value K (row a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2) (by positivity) b).comp
      (continuous_id.prodMk continuous_const)
  exact (integral_map_of_stronglyMeasurable (StoppedContinuationMeasure.measurable_value K X exit hX hr)
    (test.continuous.mul ((hv t).sub (hv s))).stronglyMeasurable).trans hjoint

end SHEStochastic.UnboundedGlobalNativeSquarePasting
