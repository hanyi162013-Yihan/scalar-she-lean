module

public import SHEStochastic.GlobalBoundedFourierMartingale

public import SHEStochastic.CanonicalFourierFluctuation
public import SHEStochastic.NativeHorizonRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.GlobalNativeFourierPathMoments
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
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
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
  (ξ : Ω → RealL2) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

include hb in
/-- The actual canonical approximation law inherits the native
sub-Gaussian fluctuation bound, with arbitrary random initial data. -/
theorem subgaussian (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hInitial : W 0 =ᵐ[μ] ξ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (K : ℝ≥0) (hK : K ≤ H) (t : ℝ≥0) :
    HasSubgaussianMGF (CanonicalFourierFluctuation.value (ι := ι) K a n t)
      (min t K * BoundedFourierInput.cap H B a n ^ 2)
      (μ.map (CanonicalNativeBrownian.bundle F μ K
        (NativeHorizonRestriction.family P K hK) W hcW)) := by
  let R := NativeHorizonRestriction.family P K hK
  have hWa (t : ℝ≥0) : Measurable[F t] (W t) :=
    ((show IsStronglyPredictable F W from hW).stronglyAdapted t).measurable
  have hBundle := CanonicalNativeBrownian.measurable_bundle F μ K R W hcW hWa
  have hx := (CanonicalFourierFluctuation.continuous (ι := ι) K a n t).measurable
  apply (HasSubgaussianMGF.id_map_iff hx.aemeasurable).mp
  rw [Measure.map_map hx hBundle]
  apply (HasSubgaussianMGF.id_map_iff (hx.comp hBundle).aemeasurable).mpr
  exact (GlobalBoundedFourierMartingale.subgaussian F μ H W hW hG hβ hβ1 B hb P e ξ a n
    hH hcW hnull hEquation (min t K) ((min_le_right _ _).trans hK)).congr
      (CanonicalFourierFluctuation.comp_bundle K a n F μ R W hcW ξ hInitial t).symm

end SHEStochastic.GlobalNativeFourierPathMoments
