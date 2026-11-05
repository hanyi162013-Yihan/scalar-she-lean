module

public import SHEStochastic.GlobalNativeFourierPathMoments
public import SHEStochastic.ContinuousStoppedMartingaleTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.GlobalNativeFourierPathMartingale
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation
open SHE.FiniteHaar AddCircle UnboundedNativeHeatEquation
open scoped NNReal ENNReal

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
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
  (ξ : Ω → RealL2) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

include hb in
/-- Original native Fourier martingales give all full-past weighted
identities on their actual canonical joint laws. -/
theorem identity (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hInitial : W 0 =ᵐ[μ] ξ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (K : ℝ≥0) (hK : K ≤ H) (s t : ℝ≥0) (hst : s ≤ t)
    (ψ : BoundedContinuousFunction (CanonicalFourierFluctuation.Space (ι := ι) K) ℝ) :
    (∫ x, ψ (CanonicalStateDriverFiltration.history K s x) *
      (CanonicalFourierFluctuation.value K a n t x-CanonicalFourierFluctuation.value K a n s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ K
        (NativeHorizonRestriction.family P K hK) W hcW)) = 0 := by
  let R := NativeHorizonRestriction.family P K hK
  let X := CanonicalNativeBrownian.bundle F μ K R W hcW
  have hWa (t : ℝ≥0) : Measurable[F t] (W t) :=
    ((show IsStronglyPredictable F W from hW).stronglyAdapted t).measurable
  have hX := CanonicalNativeBrownian.measurable_bundle F μ K R W hcW hWa
  have hPast := CanonicalFutureStateDriver.adapted_past F W hcW R.W R.continuous hWa R.adapted
    0 K (CanonicalStateDriverFiltration.clock K s)
  change Measurable[F (0+(CanonicalStateDriverFiltration.clock K s).val.toNNReal)]
    (CanonicalStateDriverFiltration.history K s ∘ X) at hPast
  rw [CanonicalFourierFluctuation.clock_time K s, zero_add] at hPast
  obtain ⟨M, _, _, _, hM, _, he⟩ := GlobalBoundedFourierMartingale.exists_version
    F μ H W hW hG hβ hβ1 B hb P e ξ a n hH hcW hnull hEquation
  have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F M hM
    (min s K) (min t K) (min_le_min_right _ hst)
    (fun sample ↦ ψ (CanonicalStateDriverFiltration.history K s (X sample)))
    (ψ.continuous.measurable.comp hPast).stronglyMeasurable ‖ψ‖
    (fun sample ↦ ψ.norm_coe_le_norm _)
  rw [integral_map hX.aemeasurable]
  · calc
      _ = ∫ sample, ψ (CanonicalStateDriverFiltration.history K s (X sample)) *
          (M (min t K) sample-M (min s K) sample) ∂μ := by
        apply integral_congr_ae
        filter_upwards [CanonicalFourierFluctuation.comp_bundle K a n F μ R W hcW ξ hInitial t,
          CanonicalFourierFluctuation.comp_bundle K a n F μ R W hcW ξ hInitial s, he]
          with sample ht hs he
        dsimp only [Function.comp_apply] at ht hs
        rw [ht, hs, he (min t K) ((min_le_right _ _).trans hK),
          he (min s K) ((min_le_right _ _).trans hK)]
      _ = 0 := hh
  · exact ((ψ.continuous.comp (WeakLimitCanonicalBrownian.continuous_history K s)).mul
      ((CanonicalFourierFluctuation.continuous K a n t).sub
        (CanonicalFourierFluctuation.continuous K a n s))).stronglyMeasurable.aestronglyMeasurable

end SHEStochastic.GlobalNativeFourierPathMartingale
