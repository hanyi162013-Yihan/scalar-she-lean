module

public import SHEStochastic.JointFourierWeakLimit
public import SHEStochastic.UnboundedJointCanonicalPathMartingale
public import SHEStochastic.JointCanonicalCylinderRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.JointFourierProblem
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open GaussianItoTest StoppedPathPasting
open scoped NNReal ENNReal Topology ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [Countable ι]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B)
  (H : ℝ≥0) (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

/-- The full compact smooth joint cylinder problem, with all state,
driver and mixed covariances. This is an explicit property of a path
law; it does not assert a native stochastic integral representation. -/
def Holds (μ : Measure (Path H (RealL2 × (ι → ℝ)))) : Prop :=
  ∀ {s d : ℕ} (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ) (driver : Fin d → ι)
    (f : State (s+d) → ℝ) (hf : ContDiff ℝ 2 f) (_ : ContDiff ℝ ∞ f) (hs : HasCompactSupport f),
    PastedCylinderMartingale.Identity H (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.generator hG hβ hβ1 B hB hb a n
        (fun j ↦ e (driver j)) driver f hf hs) μ

/-- Every compact smooth cylinder in the limiting problem is an actual
martingale in the same canonical filtration as its Brownian driver. -/
theorem martingale [DecidableEq ι]
    (μ : Measure (JointCanonicalCylinderRecognition.Space (E := RealL2) (ι := ι) H))
    [IsProbabilityMeasure μ] (h : Holds hG hβ hβ1 B hB hb H e
      (μ.map (JointStateDriverPath.pack H)))
    {s d : ℕ} (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ) (driver : Fin d → ι)
    (f : State (s+d) → ℝ) (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    Martingale (AdaptedCanonicalPathTests.martingale H (JointStateDriverPath.pack H)
      (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.generator hG hβ hβ1 B hB hb a n
        (fun j ↦ e (driver j)) driver f hf hs))
      (SHE.CanonicalStateDriverFiltration.filtration H) μ :=
  JointCanonicalCylinderRecognition.martingale H μ _ _ (h a n driver f hf hSmooth hs)

theorem limit {Gn : ℕ → ℝ → V} {Cn : ℕ → ℝ≥0}
    (hGn : ∀ k, HolderWith (Cn k) β (Gn k)) (hbn : ∀ k z, ‖Gn k z‖ ≤ B)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k) (hδlim : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z-Gn k z‖ ≤ δ k)
    (P : ℕ → ProbabilityMeasure (Path H (RealL2 × (ι → ℝ))))
    (Q : ProbabilityMeasure (Path H (RealL2 × (ι → ℝ)))) (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ k, Holds (hGn k) hβ hβ1 B hB (hbn k) H e (P k : Measure _)) :
    Holds hG hβ hβ1 B hB hb H e (Q : Measure _) := by
  intro s d a n driver f hf hSmooth hs
  exact JointFourierWeakLimit.identity hG hβ hβ1 B hB hb hGn hbn a n
    (fun j ↦ e (driver j)) driver f hf hs H δ hδ hδlim hclose P Q hlim
    (fun k ↦ hP k a n driver f hf hSmooth hs)

theorem native {Ω : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (P : FiniteScalarIto.Family F μ H ι) (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ)
    (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H) (hlt : β < 1)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedNativeHeatEquation.RandomEquation F μ H W hW hG hβ hlt P e ξ) :
    Holds hG hβ hlt.le B hB hb (min H 1) e
      (μ.map (UnboundedJointCanonicalPathMartingale.path F μ H W P hcW)) := by
  intro s d a n driver f hf hSmooth hs
  exact UnboundedJointCanonicalPathMartingale.bounded_random_identity hG hβ hlt f a n F μ H W hW
    P e driver ξ hξ hInitial hH hcW hnull hEquation hf hSmooth hs B hB hb

end SHEStochastic.JointFourierProblem
