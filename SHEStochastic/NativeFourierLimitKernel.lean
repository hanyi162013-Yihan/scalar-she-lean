module

public import SHEStochastic.NativeFourierLimitMixed
public import SHEStochastic.CanonicalFourierDisintegration
public import SHEStochastic.CanonicalInitialBrownianKernel
public import SHEStochastic.CanonicalFourierMildSolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.NativeFourierLimitKernel
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

def Supports {V ι : Type*} [Countable ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (K : ℝ≥0) (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) K)) [IsProbabilityMeasure Q]
    {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
    (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) : Prop :=
  ∀ᵐ z ∂CanonicalInitialKernel.initialLaw K Q,
    ∃ hB : ∀ d (j : Fin d → ι), FiniteBrownianLawOn
      (filtration (E := RealL2) (ι := ι) K) (CanonicalInitialKernel.kernel K Q z)
      K (fun i ↦ coordinate K (j i)) (fun i k ↦ if j i = j k then 1 else 0),
    BoundedFourierMildRecognition.HasClosedVersion (filtration K)
      (CanonicalInitialKernel.kernel K Q z) K (state K) (state_predictable K) hG hβ hβ1 B hb
      (FiniteCylindricalIto.terminalIto
        (CanonicalNativeFourierRecognition.family K (CanonicalInitialKernel.kernel K Q z) hB).toCoordinates e)
      (state K 0)

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
/-- The one ACTUAL weak limit supplies a Borel initial-state solution
kernel: almost every conditional law is a native mild solution with a
driver Brownian in its whole state-and-driver history. -/
theorem mild (hH : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → RealL2) (hInitial : ∀ k, W k 0 =ᵐ[μ] ξ)
    (hEquation : ∀ k, RandomEquation F μ H (W k) (hW k) (hGn k) hβ hβ1 (P k) e ξ)
    {G : ℝ → V} {C : ℝ≥0} (hG : HolderWith C β G) (hb : ∀ z, ‖G z‖ ≤ B)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k) (hδlim : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ k z, ‖G z-Gn k z‖ ≤ δ k)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (min H 1)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto ((NativeBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ) atTop (𝓝 Q))
    (hBrown : ∀ d (j : Fin d → ι), FiniteBrownianLawOn
      (filtration (E := RealL2) (ι := ι) (min H 1)) Q.toMeasure (min H 1)
      (fun i ↦ coordinate (min H 1) (j i)) (fun i k ↦ if j i = j k then 1 else 0)) :
    Supports (min H 1) Q.toMeasure hG hβ hβ1 B hb e := by
  let K := min H 1
  have hm (a : ℂ →L[ℝ] ℝ) (n : ℤ) := NativeFourierLimitMartingale.martingale F μ H W hcW hW
    hGn hβ hβ1 B hbn P e hH hnull ξ hInitial hEquation Q φ hlim a n
  have h4 (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
      MemLp (CanonicalFourierFluctuation.value (ι := ι) K a n t) 4 Q.toMeasure :=
    (hm a n).2 t |>.memLp (4 : ℝ≥0)
  have hs2 (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
      MemLp (CanonicalFourierDisintegration.square K hG hβ hβ1 B hb a n t) 2 Q.toMeasure := by
    let A := NativeFourierSquareTests.compensator (ι := ι) hG hβ hβ1 B hb a n K t
    change MemLp (fun x ↦ (CanonicalFourierFluctuation.value K a n t x)^2-A x) 2 Q.toMeasure
    simpa only [pow_two] using
      QuadraticMomentBounds.product_sub_memLp Q.toMeasure (h4 a n t) (h4 a n t)
        A.continuous.stronglyMeasurable.aestronglyMeasurable ‖A‖ A.norm_coe_le_norm
  have hx2 (a : ℂ →L[ℝ] ℝ) (n : ℤ) (i : ι) (t : ℝ≥0) :
      MemLp (CanonicalFourierDisintegration.mixed K hG hβ hβ1 B hb a n (e i) i t) 2 Q.toMeasure := by
    let A := NativeFourierMixedTests.compensator (ι := ι) hG hβ hβ1 B hb a n (e i) K t
    change MemLp (fun x ↦ CanonicalFourierFluctuation.value K a n t x*coordinate K i t x-A x) 2 Q.toMeasure
    exact
      QuadraticMomentBounds.product_sub_memLp Q.toMeasure (h4 a n t)
        ((CanonicalFourierDisintegration.coordinate_subgaussian K Q.toMeasure hBrown i t).memLp (4 : ℝ≥0))
        A.continuous.stronglyMeasurable.aestronglyMeasurable ‖A‖ A.norm_coe_le_norm
  have he (a : ℂ →L[ℝ] ℝ) (n : ℤ) := CanonicalFourierDisintegration.equation K hG hβ hβ1 B hb a n
    Q.toMeasure e (hm a n).1 (fun t ↦ (hm a n).2 t |>.memLp (2 : ℝ≥0))
    (NativeFourierLimitSquare.martingale F μ H W hcW hW hGn hβ hβ1 B hbn P e
      hH hnull ξ hInitial hEquation hG hb δ hδ hδlim hclose Q φ hφ hlim a n) (hs2 a n)
    (fun i ↦ NativeFourierLimitMixed.martingale F μ H W hcW hW hGn hβ hβ1 B hbn P e
      hH hnull ξ hInitial hEquation hG hb δ hδ hδlim hclose Q φ hφ hlim a n i) (hx2 a n)
  have hall := ae_all_iff.mpr fun n : ℤ ↦ (he Complex.reCLM n).and (he Complex.imCLM n)
  filter_upwards [hall, CanonicalInitialBrownianKernel.law K Q.toMeasure hBrown] with z hz hB
  refine ⟨hB, ?_⟩
  exact CanonicalFourierMildSolution.exists_closed_of_basis K (CanonicalInitialKernel.kernel K Q.toMeasure z)
    hG hβ hβ1 B hb e hB (lt_min hH (by norm_num)) (fun n ↦ ⟨(hz n).1 hB, (hz n).2 hB⟩)

end SHEStochastic.NativeFourierLimitKernel
