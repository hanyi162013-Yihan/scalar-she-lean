module

public import SHEStochastic.GlobalNativeUniformFourierPrefix
public import SHEStochastic.JointPathFiltration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalNativeFourierPasting
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
/-- The actual enlarged law has the Fourier-mode martingale identity
and a fourth moment for its entire mode trajectory. All integrability
and random-time evaluation obligations are derived from the constructed
conditional continuation estimates and the stopped source bound. -/
theorem law_identity_and_moment (R : ℕ) (hR : M ≤ R)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H))
    (hLaw : CanonicalInitialKernel.initialLaw H Q.toMeasure =
      UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput H Q.toMeasure)
    {Gcut : ℝ → V} {Ccut : ℝ≥0} (hcut : HolderWith Ccut β Gcut)
    (B : ℝ≥0) (hB : ∀ z, ‖Gcut z‖ ≤ B)
    (hFuture : ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q.toMeasure,
      CanonicalMildFourierCharacteristics.Holds H
        (CanonicalInitialKernel.kernel H Q.toMeasure u) hcut hβ hβ1 B hB e)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    PastedLinearHeatMartingale.Identity H (row (ι := ι) a n) ((n : ℝ)^2)
      (StoppedContinuationMeasure.law H (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
        μ (NativeContinuationKernel.joint H Q.toMeasure)) ∧
    MemLp (envelope H (row (ι := ι) a n) ((n : ℝ)^2)) 4
      (StoppedContinuationMeasure.law H (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
        μ (NativeContinuationKernel.joint H Q.toMeasure)) := by
  let K := H
  let X := path F μ H W P hcW
  let r := uniformExit H W hcW R
  let hX := measurable_path F μ H W hW P hcW
  let hr := UnboundedGlobalContinuation.exit_measurable F H W hW hcW R
  let κ := NativeContinuationKernel.joint K Q.toMeasure
  let Z := StoppedContinuationMeasure.state K X r
  let ν := StoppedContinuationMeasure.joint K X r hX hr μ κ
  have hZ : Measurable Z := StoppedContinuationMeasure.measurable_state K X r hX hr
  have hp : MeasurePreserving (fun ω ↦ (Z ω).1) μ (CanonicalInitialKernel.initialLaw K Q.toMeasure) := by
    refine ⟨measurable_fst.comp hZ, ?_⟩
    rw [hLaw]
    rfl
  have hi : ∀ᵐ ω ∂μ, ∀ᵐ y ∂κ (Z ω), y (origin K) = Z ω := by
    filter_upwards [hp.quasiMeasurePreserving.ae
      (NativeContinuationCharacteristics.matching_initial K Q.toMeasure hBrown)] with ω hω
    exact hω (Z ω).2
  have hf := (hp.quasiMeasurePreserving.ae
    (NativeContinuationFourierInput.properties K Q.toMeasure hcut hβ hβ1 B hB e hFuture)).mono
      fun ω hω ↦ hω (Z ω).2 a n
  have hEnv : MemLp (fun z : Ω × Path K (JointStateDriverPath.State RealL2 ι) ↦
      envelope K (row a n) ((n : ℝ)^2) z.2) 4 ν :=
    PastedLinearHeatIntegrability.future_envelope_memLp K (row a n) ((n : ℝ)^2)
      μ X r hX hr κ (fourthConstant K B a n) (fourthConstant_lt_top K B a n)
      (hf.mono fun _ h ↦ h.2)
  let D := Real.exp ((n : ℝ)^2*(K : ℝ))*‖NativeFourierHeatCoordinate.coordinate a n‖*R+
    ‖NativeFourierHeatCoordinate.coordinate a n‖*R
  have hD : ∀ᵐ ω ∂μ, ∀ t : Time K, t ≤ r ω → ‖value K (row a n) ((n : ℝ)^2) (X ω) t‖ ≤ D :=
    GlobalNativeUniformFourierPrefix.bound F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R hR a n
  constructor
  · intro s t hst test htest
    have hv (q : Time K) : Continuous (fun y : Path K (JointStateDriverPath.State RealL2 ι) ↦
        value K (row a n) ((n : ℝ)^2) y q) :=
      (continuous_value K (row a n) ((n : ℝ)^2)).comp (continuous_id.prodMk continuous_const)
    change (∫ y, test y*(value K (row a n) ((n : ℝ)^2) y t-value K (row a n) ((n : ℝ)^2) y s)
      ∂ν.map (StoppedContinuationMeasure.value K X r)) = 0
    calc
      _ = ∫ z, test (StoppedContinuationMeasure.value K X r z)*
          (value K (row a n) ((n : ℝ)^2) (StoppedContinuationMeasure.value K X r z) t-
            value K (row a n) ((n : ℝ)^2) (StoppedContinuationMeasure.value K X r z) s) ∂ν :=
        integral_map_of_stronglyMeasurable (StoppedContinuationMeasure.measurable_value K X r hX hr)
          (test.continuous.mul ((hv t).sub (hv s))).stronglyMeasurable
      _ = 0 := by
        apply PastedLinearHeatMartingale.joint_identity K (row a n) ((n : ℝ)^2) μ X r hX hr κ hi
          (hf.mono fun _ h ↦ h.1) s t hst test htest
        · exact PastedLinearHeatIntegrability.pre_integrable K (row a n) ((n : ℝ)^2) μ X r hX hr κ D hD s t test
        · exact PastedLinearHeatIntegrability.post_integrable K (row a n) ((n : ℝ)^2) μ X r hX hr κ
            (sq_nonneg _) (hEnv.integrable (by norm_num)) s t test
        · exact GlobalNativeUniformFourierPrefix.stopped_identity F μ H W hW hG hβ hβ1 P e u₀
            hH hcW hnull hEquation M hM hu₀ R hR a n s t hst test htest
  · apply (memLp_map_measure_iff (continuous_envelope K (row a n) ((n : ℝ)^2)).measurable.aestronglyMeasurable
      (StoppedContinuationMeasure.measurable_value K X r hX hr).aemeasurable).mpr
    exact PastedLinearHeatIntegrability.pasted_envelope_memLp K (row a n) ((n : ℝ)^2)
      μ X r hX hr κ (sq_nonneg _) D hD hi hEnv

include hH hnull hEquation hM hu₀ in
/-- The actual pasted Fourier mode is a genuine martingale in the full
state-and-driver filtration. -/
theorem martingale (R : ℕ) (hR : M ≤ R)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H))
    (hLaw : CanonicalInitialKernel.initialLaw H Q.toMeasure =
      UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput H Q.toMeasure)
    {Gcut : ℝ → V} {Ccut : ℝ≥0} (hcut : HolderWith Ccut β Gcut)
    (B : ℝ≥0) (hB : ∀ z, ‖Gcut z‖ ≤ B)
    (hFuture : ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q.toMeasure,
      CanonicalMildFourierCharacteristics.Holds H
        (CanonicalInitialKernel.kernel H Q.toMeasure u) hcut hβ hβ1 B hB e)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (fun q x ↦ value H (row (ι := ι) a n) ((n : ℝ)^2) x
        (AdaptedCanonicalPathTests.clock H q))
      (JointPathFiltration.filtration (E := RealL2) (ι := ι) H)
      (StoppedContinuationMeasure.law H (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
        μ (NativeContinuationKernel.joint H Q.toMeasure)) := by
  obtain ⟨hi, hm⟩ := law_identity_and_moment F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation
    M hM hu₀ R hR Q hLaw hBrown hcut B hB hFuture a n
  exact PastedLinearHeatMartingale.martingale H (row a n) ((n : ℝ)^2) _
    (JointPathFiltration.filtration H) (JointPathFiltration.evaluation_adapted H)
    (fun _ ↦ le_rfl) hi (hm.mono_exponent (by norm_num))

end SHEStochastic.UnboundedGlobalNativeFourierPasting
