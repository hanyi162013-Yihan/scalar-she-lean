module

public import SHEStochastic.GlobalNativeContinuationKernel
public import SHEStochastic.UnboundedJointNativePasting
public import SHEStochastic.UnboundedGlobalJointNativeContinuation
public import SHEStochastic.UnboundedGlobalExitInitialLaw
public import SHEStochastic.GlobalScalarVarianceNormalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.UnboundedGlobalJointNativePasting
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open StoppedPathPasting UnboundedNativeHeatEquation UnboundedGlobalUniformRegularity
open UnboundedGlobalJointCanonicalPathMartingale
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
  (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)

open UnboundedJointNativePasting

include hH hnull hEquation hM hu₀ in
/-- Instantiate joint pasting with the native continuation kernel.
There are no separate future-identity or matching-state hypotheses:
both follow from the constructed conditional native solution laws. -/
theorem law_problem (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H))
    (hLaw : CanonicalInitialKernel.initialLaw H Q.toMeasure =
      UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hSupport : GlobalNativeFourierLimitKernel.Supports H hH Q.toMeasure
      (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 (bound (G := G) (C := C) (β := β) R)
      (UnboundedCoefficientCutoff.bounded hG R) e) :
    JointFourierProblem.Holds (UnboundedCoefficientCutoff.holder hG R) hβ hβ1.le
      (bound (G := G) (C := C) (β := β) R) (bound (G := G) (C := C) (β := β) R).property
      (UnboundedCoefficientCutoff.bounded hG R) H e
      (StoppedContinuationMeasure.law H (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
        μ (NativeContinuationKernel.joint H Q.toMeasure)) := by
  let X := StoppedContinuationMeasure.state H (path F μ H W P hcW) (uniformExit H W hcW R)
  have hX : Measurable X := StoppedContinuationMeasure.measurable_state H
    (path F μ H W P hcW) (uniformExit H W hcW R) (measurable_path F μ H W hW P hcW)
      (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
  have hl : μ.map (fun sample ↦ (X sample).1) = CanonicalInitialKernel.initialLaw H Q.toMeasure := by
    rw [hLaw]
    rfl
  have hp := GlobalNativeContinuationKernel.at_reached H Q.toMeasure
    (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 (bound (G := G) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hG R) e hH hSupport μ X hX hl
  intro s d a n driver f hf hSmooth hs
  exact UnboundedGlobalJointNativeContinuation.law_identity F μ H W hW hG hβ hβ1 P e u₀ f a n driver
    hH hcW hnull hEquation M hM hu₀ hf hs hSmooth R
    (NativeContinuationKernel.joint H Q.toMeasure)
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
    (heq : UnboundedGlobalNativeEquation.Equation F μ H W hW hg hbeta hbeta1 P₀ e₀ u)
    (M₀ : ℝ) (hM₀ : 0 ≤ M₀)
    (hu : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u = ENNReal.ofReal M₀)
    (ell : ℝ) (hell : 0 < ell) (helliptic : ∀ z, ell ≤ (g z)^2)
    (R : ℕ) (hR : M₀ ≤ R) :
    ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H),
      CanonicalInitialKernel.initialLaw H Q.toMeasure =
        UnboundedGlobalExitInitialLaw.law H W hc R μ ∧
      NativeContinuationCharacteristics.BrownianInput H Q.toMeasure ∧
      (∀ᵐ u ∂UnboundedGlobalExitInitialLaw.law H W hc R μ,
        CanonicalMildFourierCharacteristics.Holds H
          (CanonicalInitialKernel.kernel H Q.toMeasure u)
          (UnboundedCoefficientCutoff.holder hg R) hbeta hbeta1
          (bound (G := g) (C := Cg) (β := beta) R) (UnboundedCoefficientCutoff.bounded hg R) e₀) ∧
      JointFourierProblem.Holds (UnboundedCoefficientCutoff.holder hg R) hbeta hbeta1.le
        (bound (G := g) (C := Cg) (β := beta) R) (bound (G := g) (C := Cg) (β := beta) R).property
        (UnboundedCoefficientCutoff.bounded hg R) H e₀
        (StoppedContinuationMeasure.law H (path F μ H W P₀ hc) (uniformExit H W hc R)
          (measurable_path F μ H W hW P₀ hc) (UnboundedGlobalContinuation.exit_measurable F H W hW hc R)
          μ (NativeContinuationKernel.joint H Q.toMeasure)) := by
  let ρ := UnboundedGlobalExitInitialLaw.law H W hc R μ
  letI : IsProbabilityMeasure ρ := UnboundedGlobalExitInitialLaw.probability H W hc F hW μ R
  have hρ : MemLp (id : RealL2 → RealL2) 2 ρ :=
    UnboundedGlobalExitInitialLaw.memLp_identity H W hc F hW μ hg hbeta hbeta1 P₀ e₀ u
      hpH hn heq M₀ hM₀ hu R hR
  let K := H
  let B := bound (G := g) (C := Cg) (β := beta) R
  have hel : ∀ z, ell ≤ (UnboundedCoefficientCutoff.coefficient g R z)^2 :=
    UnboundedCoefficientCutoff.preserves (fun v : ℝ ↦ ell ≤ v^2) helliptic R
  obtain ⟨Q, hQ, hBrown, hprops⟩ := GlobalScalarVarianceNormalization.exists_kernel
    (UnboundedCoefficientCutoff.holder hg R) hbeta F μ K
    (NativeRandomInitialKernel.restrict F μ H P₀ K le_rfl) e₀ hbeta1 B
    (UnboundedCoefficientCutoff.bounded hg R) ell hell hel hpH ρ hρ
  refine ⟨Q, hQ, hBrown, hprops.mono (fun _ h ↦ h.1), ?_⟩
  let X := StoppedContinuationMeasure.state K (path F μ H W P₀ hc) (uniformExit H W hc R)
  have hX : Measurable X := StoppedContinuationMeasure.measurable_state K (path F μ H W P₀ hc)
    (uniformExit H W hc R) (measurable_path F μ H W hW P₀ hc)
    (UnboundedGlobalContinuation.exit_measurable F H W hW hc R)
  have hpres : MeasurePreserving (fun sample ↦ (X sample).1) μ ρ := ⟨measurable_fst.comp hX, rfl⟩
  have hp := (hpres.quasiMeasurePreserving.ae hprops).mono fun sample hs ↦ hs.2 (X sample).2
  intro s d a n driver f hf hSmooth hs
  exact UnboundedGlobalJointNativeContinuation.law_identity F μ H W hW hg hbeta hbeta1 P₀ e₀ u f a n driver
    hpH hc hn heq M₀ hM₀ hu hf hs hSmooth R (NativeContinuationKernel.joint K Q.toMeasure)
    (hp.mono fun _ hprops ↦ hprops.1) (hp.mono fun _ hprops ↦ hprops.2 a n driver f hf hSmooth hs)

end SHEStochastic.UnboundedGlobalJointNativePasting
