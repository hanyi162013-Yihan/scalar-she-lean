module

public import SHEStochastic.JointFourierWeakLimit
public import SHEStochastic.UnboundedGlobalJointCanonicalPathMartingale
public import SHEStochastic.JointFourierProblem
public import SHEStochastic.JointCanonicalCylinderRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.GlobalJointFourierProblem
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

open JointFourierProblem

theorem native {Ω : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (P : FiniteScalarIto.Family F μ H ι) (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ)
    (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H) (hlt : β < 1)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hlt P e ξ) :
    Holds hG hβ hlt.le B hB hb (H) e
      (μ.map (UnboundedGlobalJointCanonicalPathMartingale.path F μ H W P hcW)) := by
  intro s d a n driver f hf hSmooth hs
  exact UnboundedGlobalJointCanonicalPathMartingale.bounded_random_identity hG hβ hlt f a n F μ H W hW
    P e driver ξ hξ hInitial hH hcW hnull hEquation hf hSmooth hs B hB hb

end SHEStochastic.GlobalJointFourierProblem
