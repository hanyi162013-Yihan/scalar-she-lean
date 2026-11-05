module

public import SHEStochastic.PositiveScalarApproximation
public import SHEStochastic.NativeSmoothWeakExistence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.NativeSmoothApproximationFamily
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier AddCircle
open PositiveScalarApproximation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

variable {Ω ι κ η : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [Countable κ] [Countable η] [DecidableEq η]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ RealHaarInput)
  (b : HilbertBasis κ ℝ RealL2)
  (q : HilbertBasis η ℝ (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))))
  {a : ℝ → ℝ} {C β : ℝ≥0} (ha : HolderWith C β a) (hβ : 0 < β) (hβ1 : β < 1)
  (ell cap : ℝ) (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)

local notation "FN" => PredictableTimeDilation.filtration F
  (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)

include P e b in
/-- The smooth variance approximations are realized by actual native
weak solutions on one common probability space and filtration. -/
theorem exists_family (hH : (H : ℝ) ≤ 1) (hpos : 0 < H)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (Z : Ω → RealL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ (W : ℕ → ℝ≥0 → Ω → RealL2) (hcW : ∀ k sample, Continuous (fun t ↦ W k t sample))
      (hW : ∀ k, StronglyMeasurable[(FN).predictable] (Function.uncurry (W k)))
      (Q : ℕ → FiniteScalarIto.Family FN μ (NativeClock.rate*H) η),
      (∀ k, W k 0 =ᵐ[μ] Z) ∧ ∀ k,
        UnboundedNativeHeatEquation.RandomEquation FN μ (NativeClock.rate*H) (W k) (hW k)
          (amplitude_holder ha hβ ell cap hell hb k) hβ hβ1 (Q k) q Z := by
  have hex (k : ℕ) : ∃ W : ℝ≥0 → Ω → RealL2,
      (∀ sample, Continuous (fun t ↦ W t sample)) ∧
      ∃ hW : StronglyMeasurable[(FN).predictable] (Function.uncurry W),
        W 0 =ᵐ[μ] Z ∧ ∃ Q : FiniteScalarIto.Family FN μ (NativeClock.rate*H) η,
          UnboundedNativeHeatEquation.RandomEquation FN μ (NativeClock.rate*H) W hW
            (amplitude_holder ha hβ ell cap hell hb k) hβ hβ1 Q q Z := by
    obtain ⟨L, hL⟩ := SmoothApproximation.boundedSmooth_lipschitz (smooth ha hβ ell cap hell hb k)
    have hLc : LipschitzWith L (fun z ↦ (variance (a := a) k z : ℂ)) := by
      simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp hL
    have hv : ∀ x y : ℝ, |variance (a := a) k x-variance (a := a) k y| ≤
        (C : ℝ)*|x-y|^(β : ℝ) := by
      intro x y
      simpa only [Real.dist_eq] using (variance_holder ha hβ ell cap hell hb k).dist_le x y
    exact NativeSmoothWeakExistence.exists_solution F μ H P e b q hH hpos hnull
      (a := variance (a := a) k) (G := amplitude (a := a) k) (α := (β : ℝ)) (K := (C : ℝ))
      (smooth ha hβ ell cap hell hb k).smooth.continuous.measurable hell
      (bounds ha hβ ell cap hell hb k) (show 0 < (β : ℝ) from hβ) (show 0 ≤ (C : ℝ) from C.2) hv
      hLc (square ha hβ ell cap hell hb k) (fun _ ↦ Real.sqrt_nonneg _)
      (amplitude_holder ha hβ ell cap hell hb k) hβ hβ1 Z hZ₀ hZ
  choose W hcW hW hi Q he using hex
  exact ⟨W, hcW, hW, Q, hi, he⟩

end SHEStochastic.NativeSmoothApproximationFamily
