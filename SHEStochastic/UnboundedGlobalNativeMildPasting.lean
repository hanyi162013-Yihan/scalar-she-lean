module

public import SHEStochastic.UnboundedGlobalNativeMixedPasting
public import SHEStochastic.UnboundedGlobalNativeCharacteristics
public import SHEStochastic.GlobalJointPathNativeFourier

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalNativeMildPasting
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





/-- The actual enlargement of the original solution by its constructed
conditional continuation kernel. -/
def law (R : ℕ) (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H))) :
    Measure (JointPathFiltration.Space (E := RealL2) (ι := ι) (H)) :=
  StoppedContinuationMeasure.law (H) (path F μ H W P hcW) (uniformExit H W hcW R)
    (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
    μ (NativeContinuationKernel.joint (H) Q.toMeasure)

instance law_probability (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H))) :
    IsProbabilityMeasure (law F μ H W hW P hcW R Q) := by unfold law; infer_instance


/-- The native bounded-cutoff mild solution on the actual pasted law. -/
def Solves (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)))
    (hLaw : CanonicalInitialKernel.initialLaw (H) Q.toMeasure = UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput (H) Q.toMeasure) : Prop :=
    let P' := UnboundedGlobalNativeCharacteristics.family F μ H W hW hG hβ hβ1 P e u₀
      hH hcW hnull hEquation M hM hu₀ R Q hLaw hBrown
    GlobalBoundedFourierRecognition.HasClosedVersion
      (JointPathFiltration.filtration (E := RealL2) (ι := ι) (H)) (law F μ H W hW P hcW R Q) (H)
      (JointPathState.state (H)) (JointPathState.predictable (H))
      (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
      (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
      (UnboundedCoefficientCutoff.bounded hG R) hH (FiniteCylindricalIto.terminalIto P'.toCoordinates e)
      (JointPathState.state (H) 0)

include hH hnull hEquation hM hu₀ in
/-- The actual pasted solution satisfies the bounded cutoff mild equation
with its full native Brownian family. The mode, square and mixed
characteristics and all their moment premises are proved internally. -/
theorem closed (R : ℕ) (hR : M ≤ R)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)))
    (hLaw : CanonicalInitialKernel.initialLaw (H) Q.toMeasure = UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput (H) Q.toMeasure)
    (hFuture : ∀ᵐ u ∂CanonicalInitialKernel.initialLaw (H) Q.toMeasure,
      CanonicalMildFourierCharacteristics.Holds (H) (CanonicalInitialKernel.kernel (H) Q.toMeasure u)
        (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
        (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
        (UnboundedCoefficientCutoff.bounded hG R) e) :
    Solves F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R Q hLaw hBrown := by
  let K := H
  let ν := law F μ H W hW P hcW R Q
  let P' := UnboundedGlobalNativeCharacteristics.family F μ H W hW hG hβ hβ1 P e u₀
    hH hcW hnull hEquation M hM hu₀ R Q hLaw hBrown
  have hP' (i : ι) (q : ℝ≥0) : P'.W i q = JointPathFiltration.driver (E := RealL2) (ι := ι) K i q := rfl
  have hbase (a : ℂ →L[ℝ] ℝ) (n : ℤ) := UnboundedGlobalNativeFourierPasting.law_identity_and_moment
    F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R hR Q hLaw hBrown
    (UnboundedCoefficientCutoff.holder hG R)
    (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hG R) hFuture a n
  apply GlobalJointPathNativeFourier.exists_closed K ν (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
    (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hG R) P' e hP' hH
  · exact fun a n ↦ (hbase a n).1
  · intro a n
    exact UnboundedGlobalNativeSquarePasting.law_identity F μ H W hW hG hβ hβ1 P e u₀
      hH hcW hnull hEquation M hM hu₀ R hR Q hLaw hBrown hFuture a n
  · intro a n i
    exact UnboundedGlobalNativeMixedPasting.law_identity F μ H W hW hG hβ hβ1 P e u₀
      hH hcW hnull hEquation M hM hu₀ R hR Q hLaw hBrown hFuture a n i
  · exact fun a n ↦ (hbase a n).2

/-- Ellipticity and the original unbounded equation construct the
continuation kernel and the actual bounded pasted mild solution. No
future equation or characteristic is an additional input. -/
theorem exists_closed {g : ℝ → ℝ} {Cg beta : ℝ≥0}
    (hg : HolderWith Cg beta g) (hbeta : 0 < beta) (hbeta1 : beta < 1)
    (P₀ : FiniteScalarIto.Family F μ H ι)
    (e₀ : HilbertBasis ι ℝ ScalarVarianceNormalization.Noise) (u : RealL2)
    (hpH : 0 < H) (hc : ∀ sample, Continuous (fun t ↦ W t sample))
    (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (heq : UnboundedGlobalNativeEquation.Equation F μ H W hW hg hbeta hbeta1 P₀ e₀ u)
    (M₀ : ℝ) (hM₀ : 0 ≤ M₀)
    (hu : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u = ENNReal.ofReal M₀)
    (ell : ℝ) (hell : 0 < ell) (helliptic : ∀ z, ell ≤ (g z)^2)
    (R : ℕ) (hR : M₀ ≤ R) :
    ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)),
      ∃ hLaw : CanonicalInitialKernel.initialLaw (H) Q.toMeasure = UnboundedGlobalExitInitialLaw.law H W hc R μ,
      ∃ hBrown : NativeContinuationCharacteristics.BrownianInput (H) Q.toMeasure,
        Solves F μ H W hW hg hbeta hbeta1 P₀ e₀ u hpH hc hn heq M₀ hM₀ hu R Q hLaw hBrown := by
  obtain ⟨Q, hLaw, hBrown, hFuture, _⟩ := UnboundedGlobalJointNativePasting.exists_law_problem
    F μ H W hW hg hbeta hbeta1 P₀ e₀ u hpH hc hn heq M₀ hM₀ hu ell hell helliptic R hR
  refine ⟨Q, hLaw, hBrown, ?_⟩
  apply closed F μ H W hW hg hbeta hbeta1 P₀ e₀ u hpH hc hn heq M₀ hM₀ hu R hR Q hLaw hBrown
  rw [hLaw]
  exact hFuture

end SHEStochastic.UnboundedGlobalNativeMildPasting
