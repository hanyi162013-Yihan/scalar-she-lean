module

public import SHEStochastic.UnboundedGlobalNativeMildPasting
public import SHEStochastic.GlobalBoundedMildUniformRegularity
public import SHEStochastic.ProjectedContinuationRecovery

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalNativeLawRecovery
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open UnboundedNativeHeatEquation UnboundedGlobalUniformRegularity StoppedPathPasting
open UnboundedGlobalJointCanonicalPathMartingale UnboundedGlobalNativeMildPasting
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

theorem source_project (sample : Ω) :
    ProjectedContinuationRecovery.project (H) (path F μ H W P hcW sample) =
      NativeContinuousPath.path (H) W hcW sample := by
  ext t
  rfl

theorem cut_eq (R : ℕ) :
    ProjectedContinuationRecovery.cut (H)
      (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) R (path F μ H W P hcW) =
        uniformExit H W hcW R := by
  funext sample
  unfold ProjectedContinuationRecovery.cut
  rw [source_project]
  rfl

theorem law_eq (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H))) :
    StoppedContinuationMeasure.law (H) (path F μ H W P hcW)
      (ProjectedContinuationRecovery.cut (H)
        (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) R (path F μ H W P hcW))
      (measurable_path F μ H W hW P hcW)
      (ProjectedContinuationRecovery.measurable_cut (H)
        (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) (L2ExtendedUniformNorm.measurable_realValue _) R
        (path F μ H W P hcW) (measurable_path F μ H W hW P hcW)) μ
      (NativeContinuationKernel.joint (H) Q.toMeasure) = law F μ H W hW P hcW R Q :=
  StoppedContinuationMeasure.law_congr_exit (H) (path F μ H W P hcW) _
    (measurable_path F μ H W hW P hcW) _ (uniformExit H W hcW R)
    (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R) (cut_eq F μ H W P hcW R) μ _

include hH hnull hEquation in
/-- The actual pasted native solution has the original deterministic
initial state. This follows from path pasting, for any continuation law. -/
theorem initial (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H))) :
    JointPathState.state (H) 0 =ᵐ[law F μ H W hW P hcW R Q] fun _ ↦ u₀ := by
  have hi := UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull
    (UnboundedGlobalNativeEquation.to_local F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hEquation)
  have hs : ∀ᵐ sample ∂μ,
      ProjectedContinuationRecovery.project (H) (path F μ H W P hcW sample) (origin (H)) = u₀ := by
    filter_upwards [hi] with sample hi
    change W (0 : ℝ).toNNReal sample = u₀
    simpa only [Real.toNNReal_zero] using hi
  have hh := ProjectedContinuationRecovery.initial (H)
    (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) (L2ExtendedUniformNorm.measurable_realValue _) R
    (path F μ H W P hcW) (measurable_path F μ H W hW P hcW) μ
    (NativeContinuationKernel.joint (H) Q.toMeasure) u₀ hs
  rw [law_eq F μ H W hW P hcW R Q] at hh
  filter_upwards [hh] with x hx
  rw [JointPathState.initial]
  exact hx

include hH hnull hEquation hM hu₀ in
/-- The bounded pasted equation supplies exactly the state-path
regularity required by Borel exit recovery. -/
theorem regularity (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)))
    (hLaw : CanonicalInitialKernel.initialLaw (H) Q.toMeasure = UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput (H) Q.toMeasure)
    (hSolves : Solves F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R Q hLaw hBrown) :
    ∀ᵐ x ∂law F μ H W hW P hcW R Q,
      Continuous (fun t ↦ L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))
        (ProjectedContinuationRecovery.project (H) x t)) ∧
      ∀ t, L2ExtendedUniformNorm.value (haarAddCircle (T := 1))
        (ProjectedContinuationRecovery.project (H) x t) ≠ ⊤ := by
  let K := H
  let P' := UnboundedGlobalNativeCharacteristics.family F μ H W hW hG hβ hβ1 P e u₀
    hH hcW hnull hEquation M hM hu₀ R Q hLaw hBrown
  have hi := initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation R Q
  have hh := GlobalBoundedMildUniformRegularity.regularity
    (JointPathFiltration.filtration (E := RealL2) (ι := ι) K) (law F μ H W hW P hcW R Q) K
    (JointPathState.state K) (JointPathState.predictable K)
    (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
    (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hG R) (FiniteCylindricalIto.terminalIto P'.toCoordinates e)
    (JointPathState.state K 0) u₀ hi hH (JointPathState.continuous K) M hM hu₀ hSolves
  filter_upwards [hh] with x hx
  have he : NativeContinuousPath.path K (JointPathState.state K) (JointPathState.continuous K) x =
      ProjectedContinuationRecovery.project K x := JointPathState.path K x
  have hprop := congrArg (fun z : Path K RealL2 ↦
    Continuous (fun t ↦ L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1)) (z t)) ∧
      ∀ t, L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) (z t) ≠ ⊤) he
  exact hprop.mp hx

include hH hnull hEquation hM hu₀ in
/-- The stopped state law of the genuine bounded pasted solution is
exactly the original stopped unbounded state law. All regularity
premises of the Borel recovery theorem are derived internally. -/
theorem stopped_law (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)))
    (hLaw : CanonicalInitialKernel.initialLaw (H) Q.toMeasure = UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput (H) Q.toMeasure)
    (hSolves : Solves F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R Q hLaw hBrown) :
    ((law F μ H W hW P hcW R Q).map (ProjectedContinuationRecovery.project (H))).map
      (BorelObservablePath.stopped (H) (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) R) =
        μ.map (fun sample ↦ BorelObservablePath.stopped (H)
          (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) R
          (NativeContinuousPath.path (H) W hcW sample)) := by
  have hc := (UnboundedGlobalUniformRegularity.regularity F μ H W hW hG hβ hβ1 P e u₀
    hH hcW hnull hEquation M hM hu₀).mono fun _ h ↦ h.1
  have hp := (regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀
    R Q hLaw hBrown hSolves).mono fun _ h ↦ h.1
  have hh := ProjectedContinuationRecovery.stopped_law (H)
    (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) (L2ExtendedUniformNorm.measurable_realValue _) R
    (path F μ H W P hcW) (measurable_path F μ H W hW P hcW) μ
    (NativeContinuationKernel.joint (H) Q.toMeasure)
    (by simpa only [source_project] using hc)
    (by simpa only [law_eq F μ H W hW P hcW R Q] using hp)
  simpa only [law_eq F μ H W hW P hcW R Q, source_project] using hh

end SHEStochastic.UnboundedGlobalNativeLawRecovery
