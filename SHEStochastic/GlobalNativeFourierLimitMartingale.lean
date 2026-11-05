module

public import SHEStochastic.GlobalNativeFourierPathMartingale
public import SHEStochastic.WeakLimitMomentMartingale
public import SHEStochastic.WeakLimitSubGaussian
public import SHEStochastic.GlobalBoundedApproximationCompactness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalNativeFourierLimitMartingale
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
  {G : ℕ → ℝ → V} {C : ℕ → ℝ≥0} {β : ℝ≥0}
  (hG : ∀ k, HolderWith (C k) β (G k)) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ k z, ‖G k z‖ ≤ B) (P : ℕ → FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

include hb in
/-- The ACTUAL approximation limit's Fourier fluctuations are native
candidate martingales, with all sub-Gaussian moment control retained.
No compact polynomial cutoff or extra representation theorem is used. -/
theorem martingale (hH : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → RealL2) (hInitial : ∀ k, W k 0 =ᵐ[μ] ξ)
    (hEquation : ∀ k, UnboundedGlobalNativeEquation.RandomEquation F μ H (W k) (hW k) (hG k) hβ hβ1 (P k) e ξ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (H)))
    (φ : ℕ → ℕ)
    (hlim : Tendsto ((GlobalBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ) atTop (𝓝 Q))
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (CanonicalFourierFluctuation.value (ι := ι) (H) a n)
      (CanonicalStateDriverFiltration.filtration (H)) (Q : Measure _) ∧
    ∀ t, HasSubgaussianMGF (CanonicalFourierFluctuation.value (ι := ι) (H) a n t)
      (min t (H)*BoundedFourierInput.cap H B a n^2) (Q : Measure _) := by
  let K := H
  let A := (GlobalBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ
  let M := CanonicalFourierFluctuation.value (ι := ι) K a n
  let c (t : ℝ≥0) := min t K*BoundedFourierInput.cap H B a n^2
  letI : MetricSpace (CanonicalFourierFluctuation.Space (ι := ι) K) :=
    TopologicalSpace.metrizableSpaceMetric _
  have hSG (k : ℕ) (t : ℝ≥0) : HasSubgaussianMGF (M t) (c t) (A k : Measure _) := by
    change HasSubgaussianMGF (M t) (c t) (μ.map _)
    exact GlobalNativeFourierPathMoments.subgaussian F μ H (W (φ k)) (hW (φ k)) (hG (φ k)) hβ hβ1
      B (hb (φ k)) (P (φ k)) e ξ a n hH (hcW (φ k)) hnull (hInitial (φ k)) (hEquation (φ k))
      K le_rfl t
  have hMom (k : ℕ) (t : ℝ≥0) := WeakLimitSubGaussian.square_bound
    (X := CanonicalFourierFluctuation.Space (ι := ι) K) (A k).toMeasure (f := M t) (c := c t) (hSG k t)
  refine ⟨?_, fun t ↦ WeakLimitSubGaussian.limit A Q hlim (M t)
    (CanonicalFourierFluctuation.continuous K a n t) (c t) (fun k ↦ hSG k t)⟩
  apply WeakLimitMomentMartingale.martingale A Q hlim
    (CanonicalStateDriverFiltration.filtration K) (CanonicalStateDriverFiltration.history K)
    (WeakLimitCanonicalBrownian.continuous_history K) (fun _ ↦ le_rfl) M
    (CanonicalFourierFluctuation.continuous K a n) (CanonicalFourierFluctuation.adapted K a n)
    (fun t ↦ 1+48*Real.exp (1/2 : ℝ)*(c t : ℝ)^2)
    (fun k t ↦ (hMom k t).1) (fun k t ↦ (hMom k t).2)
  intro k s t hst ψ
  change (∫ x, ψ (CanonicalStateDriverFiltration.history K s x) *
    (M t x-M s x) ∂μ.map _) = 0
  exact GlobalNativeFourierPathMartingale.identity F μ H (W (φ k)) (hW (φ k)) (hG (φ k)) hβ hβ1
    B (hb (φ k)) (P (φ k)) e ξ a n hH (hcW (φ k)) hnull (hInitial (φ k)) (hEquation (φ k))
    K le_rfl s t hst ψ

end SHEStochastic.GlobalNativeFourierLimitMartingale
