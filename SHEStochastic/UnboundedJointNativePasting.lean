module

public import SHEStochastic.NativeContinuationKernel
public import SHEStochastic.UnboundedJointNativeContinuation
public import SHEStochastic.UnboundedExitInitialLaw
public import SHEStochastic.ScalarVarianceNormalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.UnboundedJointNativePasting
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open StoppedPathPasting UnboundedNativeHeatEquation UnboundedNativeUniformRegularity
open UnboundedJointCanonicalPathMartingale
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)

def bound (R : ℝ≥0) : ℝ≥0 := ⟨‖G 0‖+(C : ℝ)*(R : ℝ)^(β : ℝ), by positivity⟩

include hH hnull hEquation hM hu₀ in
/-- Instantiate joint pasting with the native continuation kernel.
There are no separate future-identity or matching-state hypotheses:
both follow from the constructed conditional native solution laws. -/
theorem law_problem (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (min H 1)))
    (hLaw : CanonicalInitialKernel.initialLaw (min H 1) Q.toMeasure =
      UnboundedExitInitialLaw.law H W hcW R μ)
    (hSupport : NativeFourierLimitKernel.Supports (min H 1) Q.toMeasure
      (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 (bound (G := G) (C := C) (β := β) R)
      (UnboundedCoefficientCutoff.bounded hG R) e) :
    JointFourierProblem.Holds (UnboundedCoefficientCutoff.holder hG R) hβ hβ1.le
      (bound (G := G) (C := C) (β := β) R) (bound (G := G) (C := C) (β := β) R).property
      (UnboundedCoefficientCutoff.bounded hG R) (min H 1) e
      (StoppedContinuationMeasure.law (min H 1) (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedNativeContinuation.exit_measurable F H W hW hcW R)
        μ (NativeContinuationKernel.joint (min H 1) Q.toMeasure)) := by
  let X := StoppedContinuationMeasure.state (min H 1) (path F μ H W P hcW) (uniformExit H W hcW R)
  have hX : Measurable X := StoppedContinuationMeasure.measurable_state (min H 1)
    (path F μ H W P hcW) (uniformExit H W hcW R) (measurable_path F μ H W hW P hcW)
      (UnboundedNativeContinuation.exit_measurable F H W hW hcW R)
  have hl : μ.map (fun sample ↦ (X sample).1) = CanonicalInitialKernel.initialLaw (min H 1) Q.toMeasure := by
    rw [hLaw]
    rfl
  have hp := NativeContinuationKernel.at_reached (min H 1) Q.toMeasure
    (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 (bound (G := G) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hG R) e (lt_min hH (by norm_num)) (min_le_right _ _) hSupport μ X hX hl
  intro s d a n driver f hf hSmooth hs
  exact UnboundedJointNativeContinuation.law_identity F μ H W hW hG hβ hβ1 P e u₀ f a n driver
    hH hcW hnull hEquation M hM hu₀ hf hs hSmooth R
    (NativeContinuationKernel.joint (min H 1) Q.toMeasure)
    (hp.mono fun _ hprops ↦ hprops.1)
    (hp.mono fun _ hprops ↦ hprops.2 a n driver f hf hSmooth hs)

/-- The scalar continuation kernel is constructed at the actual exit
distribution. Thus the pasted bounded-cutoff joint problem follows from
the original unbounded native equation and ellipticity alone. -/
theorem exists_law_problem {g : ℝ → ℝ} {Cg beta : ℝ≥0}
    (hg : HolderWith Cg beta g) (hbeta : 0 < beta) (hbeta1 : beta < 1)
    (P₀ : FiniteScalarIto.Family F μ H ι)
    (e₀ : HilbertBasis ι ℝ ScalarVarianceNormalization.Noise) (u : RealL2)
    (hpH : 0 < H) (hc : ∀ sample, Continuous (fun t ↦ W t sample))
    (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (heq : Equation F μ H W hW hg hbeta hbeta1 P₀ e₀ u)
    (M₀ : ℝ) (hM₀ : 0 ≤ M₀)
    (hu : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u = ENNReal.ofReal M₀)
    (ell : ℝ) (hell : 0 < ell) (helliptic : ∀ z, ell ≤ (g z)^2)
    (R : ℕ) (hR : M₀ ≤ R) :
    ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (min H 1)),
      CanonicalInitialKernel.initialLaw (min H 1) Q.toMeasure =
        UnboundedExitInitialLaw.law H W hc R μ ∧
      NativeContinuationCharacteristics.BrownianInput (min H 1) Q.toMeasure ∧
      (∀ᵐ u ∂UnboundedExitInitialLaw.law H W hc R μ,
        CanonicalMildFourierCharacteristics.Holds (min H 1)
          (CanonicalInitialKernel.kernel (min H 1) Q.toMeasure u)
          (UnboundedCoefficientCutoff.holder hg R) hbeta hbeta1
          (bound (G := g) (C := Cg) (β := beta) R) (UnboundedCoefficientCutoff.bounded hg R) e₀) ∧
      JointFourierProblem.Holds (UnboundedCoefficientCutoff.holder hg R) hbeta hbeta1.le
        (bound (G := g) (C := Cg) (β := beta) R) (bound (G := g) (C := Cg) (β := beta) R).property
        (UnboundedCoefficientCutoff.bounded hg R) (min H 1) e₀
        (StoppedContinuationMeasure.law (min H 1) (path F μ H W P₀ hc) (uniformExit H W hc R)
          (measurable_path F μ H W hW P₀ hc) (UnboundedNativeContinuation.exit_measurable F H W hW hc R)
          μ (NativeContinuationKernel.joint (min H 1) Q.toMeasure)) := by
  let ρ := UnboundedExitInitialLaw.law H W hc R μ
  letI : IsProbabilityMeasure ρ := UnboundedExitInitialLaw.probability H W hc F hW μ R
  have hρ : MemLp (id : RealL2 → RealL2) 2 ρ :=
    UnboundedExitInitialLaw.memLp_identity H W hc F hW μ hg hbeta hbeta1 P₀ e₀ u
      hpH hn heq M₀ hM₀ hu R hR
  let K := min H 1
  let B := bound (G := g) (C := Cg) (β := beta) R
  have hel : ∀ z, ell ≤ (UnboundedCoefficientCutoff.coefficient g R z)^2 :=
    UnboundedCoefficientCutoff.preserves (fun v : ℝ ↦ ell ≤ v^2) helliptic R
  obtain ⟨Q, hQ, hBrown, hprops⟩ := ScalarVarianceNormalization.exists_kernel
    (UnboundedCoefficientCutoff.holder hg R) hbeta F μ K
    (NativeRandomInitialKernel.restrict F μ H P₀ K (min_le_left _ _)) e₀ hbeta1 B
    (UnboundedCoefficientCutoff.bounded hg R) ell hell hel (lt_min hpH (by norm_num)) (min_le_right _ _) ρ hρ
  refine ⟨Q, hQ, hBrown, hprops.mono (fun _ h ↦ h.1), ?_⟩
  let X := StoppedContinuationMeasure.state K (path F μ H W P₀ hc) (uniformExit H W hc R)
  have hX : Measurable X := StoppedContinuationMeasure.measurable_state K (path F μ H W P₀ hc)
    (uniformExit H W hc R) (measurable_path F μ H W hW P₀ hc)
    (UnboundedNativeContinuation.exit_measurable F H W hW hc R)
  have hpres : MeasurePreserving (fun sample ↦ (X sample).1) μ ρ := ⟨measurable_fst.comp hX, rfl⟩
  have hp := (hpres.quasiMeasurePreserving.ae hprops).mono fun sample hs ↦ hs.2 (X sample).2
  intro s d a n driver f hf hSmooth hs
  exact UnboundedJointNativeContinuation.law_identity F μ H W hW hg hbeta hbeta1 P₀ e₀ u f a n driver
    hpH hc hn heq M₀ hM₀ hu hf hs hSmooth R (NativeContinuationKernel.joint K Q.toMeasure)
    (hp.mono fun _ hprops ↦ hprops.1) (hp.mono fun _ hprops ↦ hprops.2 a n driver f hf hSmooth hs)

end SHEStochastic.UnboundedJointNativePasting
