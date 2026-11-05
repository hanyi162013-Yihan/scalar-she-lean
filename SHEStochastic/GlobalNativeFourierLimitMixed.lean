module

public import SHEStochastic.GlobalNativeFourierMixedTests
public import SHEStochastic.GlobalNativeFourierLimitSquare

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalNativeFourierLimitMixed
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation
open SHE.FiniteHaar AddCircle UnboundedNativeHeatEquation
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

include hbn in
/-- Every mixed Fourier/driver compensator survives the actual joint
approximation limit. This retains the noise information required by
the native stochastic-integral recognition theorem. -/
theorem martingale (hH : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → RealL2) (hInitial : ∀ k, W k 0 =ᵐ[μ] ξ)
    (hEquation : ∀ k, UnboundedGlobalNativeEquation.RandomEquation F μ H (W k) (hW k) (hGn k) hβ hβ1 (P k) e ξ)
    {G : ℝ → V} {C : ℝ≥0} (hG : HolderWith C β G) (hb : ∀ z, ‖G z‖ ≤ B)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k) (hδlim : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z-Gn k z‖ ≤ δ k)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto ((GlobalBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ) atTop (𝓝 Q))
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) (i : ι) :
    Martingale (fun t x ↦ CanonicalFourierFluctuation.value (ι := ι) (H) a n t x *
      CanonicalStateDriverFiltration.coordinate (H) i t x -
      NativeFourierMixedTests.compensator hG hβ hβ1 B hb a n (e i) (H) t x)
      (CanonicalStateDriverFiltration.filtration (H)) (Q : Measure _) := by
  let K := H
  let L := (GlobalBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ
  let M := CanonicalFourierFluctuation.value (ι := ι) K a n
  let D := CanonicalStateDriverFiltration.coordinate (E := RealL2) K i
  let c (t : ℝ≥0) := min t K*BoundedFourierInput.cap H B a n^2
  let A := NativeFourierMixedTests.compensator (ι := ι) hG hβ hβ1 B hb a n (e i) K
  let An (k : ℕ) := NativeFourierMixedTests.compensator (ι := ι) (hGn (φ k)) hβ hβ1 B (hbn (φ k)) a n (e i) K
  letI : MetricSpace (CanonicalFourierFluctuation.Space (ι := ι) K) :=
    TopologicalSpace.metrizableSpaceMetric _
  have hSG (k : ℕ) (t : ℝ≥0) : HasSubgaussianMGF (M t) (c t) (L k : Measure _) := by
    change HasSubgaussianMGF (M t) (c t) (μ.map _)
    exact GlobalNativeFourierPathMoments.subgaussian F μ H (W (φ k)) (hW (φ k)) (hGn (φ k)) hβ hβ1
      B (hbn (φ k)) (P (φ k)) e ξ a n hH (hcW (φ k)) hnull (hInitial (φ k)) (hEquation (φ k)) K le_rfl t
  have hDG (k : ℕ) (t : ℝ≥0) : HasSubgaussianMGF (D t) (min t K) (L k : Measure _) := by
    change HasSubgaussianMGF (D t) (min t K) (μ.map _)
    exact CanonicalBrownianSubGaussian.coordinate F μ K
      (NativeHorizonRestriction.family (P (φ k)) K le_rfl) (W (φ k)) (hcW (φ k))
      (fun t ↦ ((show IsStronglyPredictable F (W (φ k)) from hW (φ k)).stronglyAdapted t).measurable) i t
  have hA : StronglyAdapted (CanonicalStateDriverFiltration.filtration K) (fun t x ↦ A t x) :=
    CanonicalFourierCompensator.adapted K ((n : ℝ)^2) (sq_nonneg _)
      (NativeFourierCompensatorValue.mixed hG hβ hβ1 B hb a n (e i))
  have hAc (t : ℝ≥0) : Tendsto (fun k ↦ ‖A t-An k t‖) atTop (𝓝 0) :=
    NativeFourierMixedTests.compensator_limit hG hβ hβ1 B hb a n (fun k ↦ hGn (φ k))
      (fun k ↦ hbn (φ k)) (δ ∘ φ) (fun k ↦ hδ (φ k)) (hδlim.comp hφ.tendsto_atTop)
      (fun k ↦ hclose (φ k)) (e i) K t
  change Martingale (WeakLimitCompensatedProducts.value M D A) _ _
  apply WeakLimitCompensatedProducts.martingale L Q hlim
    (CanonicalStateDriverFiltration.filtration K) (CanonicalStateDriverFiltration.history K)
    (WeakLimitCanonicalBrownian.continuous_history K) (fun _ ↦ le_rfl) M D
    (CanonicalFourierFluctuation.continuous K a n) (WeakLimitCanonicalBrownian.continuous_coordinate K i)
    (CanonicalFourierFluctuation.adapted K a n)
    (fun t ↦ (CanonicalStateDriverFiltration.coordinate_adapted K i t).stronglyMeasurable)
    c (fun t ↦ min t K) hSG hDG A An hA hAc
  intro k s t hst ψ
  change (∫ x, ψ (CanonicalStateDriverFiltration.history K s x)*
    (WeakLimitCompensatedProducts.value M D (An k) t x-
      WeakLimitCompensatedProducts.value M D (An k) s x) ∂μ.map _) = 0
  exact GlobalNativeFourierMixedTests.identity F μ H (W (φ k)) (hW (φ k)) (hGn (φ k)) hβ hβ1
    B (hbn (φ k)) (P (φ k)) e ξ a n hH (hcW (φ k)) hnull (hInitial (φ k)) (hEquation (φ k))
    K le_rfl i s t hst ψ

end SHEStochastic.GlobalNativeFourierLimitMixed
