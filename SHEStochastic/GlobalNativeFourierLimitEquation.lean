module

public import SHEStochastic.GlobalNativeFourierLimitMixed
public import SHEStochastic.CanonicalNativeFourierRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalNativeFourierLimitEquation
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation
open SHE.FiniteHaar AddCircle UnboundedNativeHeatEquation CanonicalStateDriverFiltration
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℕ → ℝ≥0 → Ω → RealL2) (hcW : ∀ k sample, Continuous (fun t ↦ W k t sample))
  (hW : ∀ k, StronglyMeasurable[F.predictable] (Function.uncurry (W k)))
  {Gn : ℕ → ℝ → V} {Cn : ℕ → ℝ≥0} {β : ℝ≥0}
  (hGn : ∀ k, HolderWith (Cn k) β (Gn k)) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hbn : ∀ k z, ‖Gn k z‖ ≤ B) (P : ℕ → FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

include hbn in
/-- The actual joint weak limit solves every native Fourier equation
with the retained Brownian family and the original coefficient. The
seven stochastic packages supply the integral; no representation axiom
is added to obtain this conclusion. -/
theorem equation (hH : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → RealL2) (hInitial : ∀ k, W k 0 =ᵐ[μ] ξ)
    (hEquation : ∀ k, UnboundedGlobalNativeEquation.RandomEquation F μ H (W k) (hW k) (hGn k) hβ hβ1 (P k) e ξ)
    {G : ℝ → V} {C : ℝ≥0} (hG : HolderWith C β G) (hb : ∀ z, ‖G z‖ ≤ B)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k) (hδlim : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z-Gn k z‖ ≤ δ k)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto ((GlobalBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ) atTop (𝓝 Q))
    (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn
      (filtration (E := RealL2) (ι := ι) (H)) Q.toMeasure
      (H) (fun i ↦ coordinate (H) (a i)) (fun i j ↦ if a i = a j then 1 else 0))
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    CanonicalNativeFourierRecognition.Solves (H) (Q : Measure _) hG hβ hβ1 B hb e hBrown a n := by
  obtain ⟨hm, hsg⟩ := GlobalNativeFourierLimitMartingale.martingale F μ H W hcW hW hGn hβ hβ1
    B hbn P e hH hnull ξ hInitial hEquation Q φ hlim a n
  apply CanonicalNativeFourierRecognition.equation (H) Q.toMeasure hG hβ hβ1 B hb e hBrown a n
  · exact hm
  · exact fun t _ ↦ (hsg t).memLp (2 : ℝ≥0)
  · exact GlobalNativeFourierLimitSquare.martingale F μ H W hcW hW hGn hβ hβ1 B hbn P e
      hH hnull ξ hInitial hEquation hG hb δ hδ hδlim hclose Q φ hφ hlim a n
  · exact fun i ↦ GlobalNativeFourierLimitMixed.martingale F μ H W hcW hW hGn hβ hβ1 B hbn P e
      hH hnull ξ hInitial hEquation hG hb δ hδ hδlim hclose Q φ hφ hlim a n i

end SHEStochastic.GlobalNativeFourierLimitEquation
