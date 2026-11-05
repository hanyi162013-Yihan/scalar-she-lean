module

public import SHEStochastic.NativeFourierSquareTests
public import SHEStochastic.NativeFourierLimitMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeFourierLimitSquare
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
/-- The limiting Fourier square has the correct compensated
martingale, obtained from the actual approximations' fourth moments
and uniformly converging coefficient covariances. -/
theorem martingale (hH : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → RealL2) (hInitial : ∀ k, W k 0 =ᵐ[μ] ξ)
    (hEquation : ∀ k, RandomEquation F μ H (W k) (hW k) (hGn k) hβ hβ1 (P k) e ξ)
    {G : ℝ → V} {C : ℝ≥0} (hG : HolderWith C β G) (hb : ∀ z, ‖G z‖ ≤ B)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k) (hδlim : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z-Gn k z‖ ≤ δ k)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (min H 1)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto ((NativeBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ) atTop (𝓝 Q))
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (fun t x ↦ (CanonicalFourierFluctuation.value (ι := ι) (min H 1) a n t x)^2-
      NativeFourierSquareTests.compensator hG hβ hβ1 B hb a n (min H 1) t x)
      (CanonicalStateDriverFiltration.filtration (min H 1)) (Q : Measure _) := by
  let K := min H 1
  let L := (NativeBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ
  let M := CanonicalFourierFluctuation.value (ι := ι) K a n
  let c (t : ℝ≥0) := min t K*BoundedFourierInput.cap H B a n^2
  let A := NativeFourierSquareTests.compensator (ι := ι) hG hβ hβ1 B hb a n K
  let An (k : ℕ) := NativeFourierSquareTests.compensator (ι := ι) (hGn (φ k)) hβ hβ1 B (hbn (φ k)) a n K
  letI : MetricSpace (CanonicalFourierFluctuation.Space (ι := ι) K) :=
    TopologicalSpace.metrizableSpaceMetric _
  have hSG (k : ℕ) (t : ℝ≥0) : HasSubgaussianMGF (M t) (c t) (L k : Measure _) := by
    change HasSubgaussianMGF (M t) (c t) (μ.map _)
    exact NativeFourierPathMoments.subgaussian F μ H (W (φ k)) (hW (φ k)) (hGn (φ k)) hβ hβ1
      B (hbn (φ k)) (P (φ k)) e ξ a n hH (hcW (φ k)) hnull (hInitial (φ k)) (hEquation (φ k))
      K le_rfl t
  have hA : StronglyAdapted (CanonicalStateDriverFiltration.filtration K) (fun t x ↦ A t x) :=
    CanonicalFourierCompensator.adapted K (2*(n : ℝ)^2) (by positivity)
      (NativeFourierCompensatorValue.diagonal hG hβ hβ1 B hb a n)
  have hAc (t : ℝ≥0) : Tendsto (fun k ↦ ‖A t-An k t‖) atTop (𝓝 0) :=
    NativeFourierSquareTests.compensator_limit hG hβ hβ1 B hb a n (fun k ↦ hGn (φ k))
      (fun k ↦ hbn (φ k)) (δ ∘ φ) (fun k ↦ hδ (φ k)) (hδlim.comp hφ.tendsto_atTop)
      (fun k ↦ hclose (φ k)) K t
  have ht (k : ℕ) (s t : ℝ≥0) (hst : s ≤ t)
      (ψ : BoundedContinuousFunction (CanonicalFourierFluctuation.Space (ι := ι) K) ℝ) :
      (∫ x, ψ (CanonicalStateDriverFiltration.history K s x)*
        (WeakLimitCompensatedProducts.value M M (An k) t x-
          WeakLimitCompensatedProducts.value M M (An k) s x) ∂(L k : Measure _)) = 0 := by
    change (∫ x, ψ (CanonicalStateDriverFiltration.history K s x)*
      (WeakLimitCompensatedProducts.value M M (An k) t x-
        WeakLimitCompensatedProducts.value M M (An k) s x) ∂μ.map _) = 0
    exact NativeFourierSquareTests.identity F μ H (W (φ k)) (hW (φ k)) (hGn (φ k)) hβ hβ1
      B (hbn (φ k)) (P (φ k)) e ξ a n hH (hcW (φ k)) hnull (hInitial (φ k)) (hEquation (φ k))
      K le_rfl s t hst ψ
  have hm := WeakLimitCompensatedProducts.martingale L Q hlim
    (CanonicalStateDriverFiltration.filtration K) (CanonicalStateDriverFiltration.history K)
    (WeakLimitCanonicalBrownian.continuous_history K) (fun _ ↦ le_rfl) M M
    (CanonicalFourierFluctuation.continuous K a n) (CanonicalFourierFluctuation.continuous K a n)
    (CanonicalFourierFluctuation.adapted K a n) (CanonicalFourierFluctuation.adapted K a n)
    c c hSG hSG A An hA hAc ht
  have he : (fun t x ↦ M t x^2-A t x) = WeakLimitCompensatedProducts.value M M A := by
    funext t x
    change M t x^2-A t x = M t x*M t x-A t x
    rw [pow_two]
  change Martingale (fun t x ↦ M t x^2-A t x) _ _
  rw [he]
  exact hm

end SHEStochastic.NativeFourierLimitSquare
