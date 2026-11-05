module

public import SHEStochastic.NativeFourierLimitKernel
public import SHEStochastic.JointFourierTranslation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.NativeContinuationKernel
open MeasureTheory ProbabilityTheory SHE SHE.DyadicApproximation SHE.FiniteHaar
open CanonicalStateDriverFiltration StoppedPathPasting
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {V ι : Type*} [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (H : ℝ≥0) (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (e : HilbertBasis ι ℝ (Lp V 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))))

def joint : Kernel (RealL2 × (ι → ℝ)) (Path H (RealL2 × (ι → ℝ))) :=
  JointStateDriverPath.continuationKernel H (CanonicalInitialKernel.kernel H Q)

instance : IsMarkovKernel (joint H Q) := by unfold joint; infer_instance

/-- The constructed native kernel has exactly the two properties used
by pasting, on one initial-state event and for every joining driver value. -/
theorem properties (hH : 0 < H) (hH1 : H ≤ 1)
    (h : NativeFourierLimitKernel.Supports H Q hG hβ hβ1 B hb e) :
    ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q, ∀ v : ι → ℝ,
      (∀ᵐ y ∂joint H Q (u,v), y (origin H) = (u,v)) ∧
      JointFourierProblem.Holds hG hβ hβ1.le B B.property hb H e (joint H Q (u,v)) := by
  filter_upwards [h, CanonicalInitialKernel.matching_initial H Q] with u hu hi v
  obtain ⟨hBrown, hMild⟩ := hu
  let P := CanonicalNativeFourierRecognition.family H (CanonicalInitialKernel.kernel H Q u) hBrown
  refine ⟨?_, ?_⟩
  · apply JointStateDriverPath.continuationKernel_initial H (CanonicalInitialKernel.kernel H Q) (u,v)
    · filter_upwards [hi] with x hx
      simpa [state, clock, origin] using hx
    · filter_upwards [ae_all_iff.mpr fun i ↦ FiniteScalarIto.zero_ae P.toCoordinates i] with x hx i
      have hz : coordinate H i 0 x = 0 := hx i
      simpa [coordinate, clock, origin] using hz
  · intro s d a n driver f hf hSmooth hs
    exact JointFourierTranslation.continuation_problem hG hβ hβ1.le B B.property hb H e
      (CanonicalInitialKernel.kernel H Q) (u,v)
      (CanonicalFourierMildSolution.joint_problem H (CanonicalInitialKernel.kernel H Q u)
        hG hβ hβ1 B hb e hBrown hH hH1 hMild) a n driver f hf hSmooth hs

/-- Only the distribution of actually reached states is required.
The joining driver's value may depend arbitrarily on the original past. -/
theorem at_reached (hH : 0 < H) (hH1 : H ≤ 1)
    (h : NativeFourierLimitKernel.Supports H Q hG hβ hβ1 B hb e)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → RealL2 × (ι → ℝ)) (hX : Measurable X)
    (hLaw : μ.map (fun sample ↦ (X sample).1) = CanonicalInitialKernel.initialLaw H Q) :
    ∀ᵐ sample ∂μ,
      (∀ᵐ y ∂joint H Q (X sample), y (origin H) = X sample) ∧
      JointFourierProblem.Holds hG hβ hβ1.le B B.property hb H e (joint H Q (X sample)) := by
  have hp : MeasurePreserving (fun sample ↦ (X sample).1) μ (CanonicalInitialKernel.initialLaw H Q) :=
    ⟨measurable_fst.comp hX, hLaw⟩
  filter_upwards [hp.quasiMeasurePreserving.ae (properties H Q hG hβ hβ1 B hb e hH hH1 h)] with sample hs
  exact hs (X sample).2

end SHEStochastic.NativeContinuationKernel
