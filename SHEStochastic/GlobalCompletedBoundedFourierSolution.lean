module

public import SHEStochastic.GlobalBoundedFourierPullback
public import SHEStochastic.CompletedBoundedFourierSolution
public import SHEStochastic.GlobalBoundedMildHeatEquation
public import SHEStochastic.RandomInitialBrownianFamily
public import SHEStochastic.GlobalJointFourierProblem

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalCompletedBoundedFourierSolution
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ μ F
local notation "μc" => IndependentNoiseCompletion.measure ρ μ

open CompletedBoundedFourierSolution

theorem equation (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hFourier : GlobalBoundedFourierRecognition.FourierEquation F μ H W hW hG hβ hβ1 B hb
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ) :
    UnboundedGlobalNativeEquation.RandomEquation Fc μc H (state μ W) (predictable F μ W hW)
      hG hβ hβ1 (RandomInitialBrownianFamily.family ρ μ F H P) e (ξ ∘ Prod.snd) := by
  let Q := RandomInitialBrownianFamily.family ρ μ F H P
  have hF := GlobalBoundedFourierPullback.equation (Ξ := RandomInitialBrownianFamily.Space ρ μ)
    (D := Fc) Prod.snd (IndependentNoiseCompletion.snd_preserving ρ μ)
    (filtered F μ) W hW hG hβ hβ1 B hb P Q e (fun _ _ _ ↦ rfl) ξ hFourier
  have hm := GlobalBoundedFourierRecognition.exists_closed Fc μc H (state μ W) (predictable F μ W hW)
    hG hβ hβ1 B hb Q e (ξ ∘ Prod.snd) hH (fun sample ↦ hcW sample.2) hF
  exact GlobalBoundedMildHeatEquation.equation Fc μc H (state μ W) (predictable F μ W hW)
    hG hβ hβ1 B hb Q e hH (fun sample ↦ hcW sample.2)
    (RandomInitialBrownianFamily.contains_null ρ μ F) (ξ ∘ Prod.snd) hm

theorem equation_of_mild (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hMild : GlobalBoundedFourierRecognition.HasClosedVersion F μ H W hW hG hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ) :
    UnboundedGlobalNativeEquation.RandomEquation Fc μc H (state μ W) (predictable F μ W hW)
      hG hβ hβ1 (RandomInitialBrownianFamily.family ρ μ F H P) e (ξ ∘ Prod.snd) :=
  equation F μ H W hW hG hβ hβ1 B hb P e ξ hH hcW
    (GlobalBoundedFourierRecognition.fourier_of_closed F μ H W hW hG hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ hMild)

/-- Completing the probability space does not change its joint path
law. Thus a native mild solution already solves the full joint cylinder
problem on its original measurable space. -/
theorem joint_problem (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ)
    (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hMild : GlobalBoundedFourierRecognition.HasClosedVersion F μ H W hW hG hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ) :
    JointFourierProblem.Holds hG hβ hβ1.le B B.property hb (H) e
      (μ.map (UnboundedGlobalJointCanonicalPathMartingale.path F μ H W P hcW)) := by
  intro s d a n driver f hf hSmooth hs
  let Q := RandomInitialBrownianFamily.family ρ μ F H P
  let hc := fun sample : RandomInitialBrownianFamily.Space ρ μ ↦ hcW sample.2
  have he := equation_of_mild F μ H W hW hG hβ hβ1 B hb P e ξ hH hcW hMild
  have hi : (state μ W) 0 =ᵐ[μc] ξ ∘ Prod.snd :=
    (IndependentNoiseCompletion.snd_preserving ρ μ).quasiMeasurePreserving.ae hInitial
  have hh : PastedCylinderMartingale.Identity (H)
      (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.generator hG hβ hβ1.le B B.property hb a n
        (fun j ↦ e (driver j)) driver f hf hs)
      ((μc).map (UnboundedGlobalJointCanonicalPathMartingale.path Fc μc H (state μ W) Q hc)) :=
    GlobalJointFourierProblem.native hG hβ B B.property hb H e
    Fc μc (state μ W) (predictable F μ W hW) Q (ξ ∘ Prod.snd)
    (hξ.comp_measurable (filtered F μ 0)) hi hH hβ1 hc
    (RandomInitialBrownianFamily.contains_null ρ μ F) he a n driver f hf hSmooth hs
  have hpath : UnboundedGlobalJointCanonicalPathMartingale.path Fc μc H (state μ W) Q hc =
      UnboundedGlobalJointCanonicalPathMartingale.path F μ H W P hcW ∘ Prod.snd := rfl
  rw [hpath, ← Measure.map_map
    (UnboundedGlobalJointCanonicalPathMartingale.measurable_path F μ H W hW P hcW)
    (IndependentNoiseCompletion.snd_preserving ρ μ).measurable,
    (IndependentNoiseCompletion.snd_preserving ρ μ).map_eq] at hh
  exact hh

end SHEStochastic.GlobalCompletedBoundedFourierSolution
