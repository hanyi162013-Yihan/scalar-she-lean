module

public import SHEStochastic.GlobalNativeSmoothApproximationFamily
public import SHEStochastic.GlobalNativeBoundedWeakLimit
public import SHEStochastic.GlobalNativeBoundedContinuationKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.GlobalNativePositiveWeakExistence
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier AddCircle
open PositiveScalarApproximation CanonicalStateDriverFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

abbrev horizon (H : ℝ≥0) := NativeClock.rate*H

variable {Ω ι κ η : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [Countable κ] [Countable η] [DecidableEq η]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ RealHaarInput)
  (b : HilbertBasis κ ℝ RealL2)
  (q : HilbertBasis η ℝ (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))))
  {a : ℝ → ℝ} {C β : ℝ≥0} (ha : HolderWith C β a) (hβ : 0 < β) (hβ1 : β < 1)
  (ell cap : ℝ) (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)

include P e b in
/-- Bounded elliptic Holder variances have an actual native weak mild
solution with arbitrary random L2 initial data. Smooth approximation,
tightness, retained Brownian laws and native integral recognition are
all supplied by the preceding proofs. -/
theorem exists_solution (hpos : 0 < H)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (Z : Ω → RealL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := η) (horizon H)))
      (hBrown : ∀ d (j : Fin d → η), FiniteBrownianLawOn
        (filtration (E := RealL2) (ι := η) (horizon H)) Q.toMeasure (horizon H)
        (fun i ↦ coordinate (horizon H) (j i)) (fun i k ↦ if j i = j k then 1 else 0)),
      Q.toMeasure.map (NativeApproximationInitialLaw.initial (horizon H)) =
        μ.map (fun sample ↦ (Z sample, fun _ : η ↦ (0 : ℝ))) ∧
      GlobalBoundedFourierRecognition.HasClosedVersion (filtration (horizon H)) Q.toMeasure (horizon H)
        (state (horizon H)) (state_predictable (horizon H)) (root_holder ha hβ ell cap hell hb)
        hβ hβ1 (bound cap) (root_bound ell cap hb) (mul_pos NativeClock.rate_pos hpos)
        (FiniteCylindricalIto.terminalIto
          (CanonicalNativeFourierRecognition.family (horizon H) Q.toMeasure hBrown).toCoordinates q)
        (state (horizon H) 0) := by
  obtain ⟨W, hcW, hW, R, hi, he⟩ := GlobalNativeSmoothApproximationFamily.exists_family F μ H P e b q
    ha hβ hβ1 ell cap hell hb hpos hnull Z hZ₀ hZ
  let FN := PredictableTimeDilation.filtration F
    (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)
  exact GlobalNativeBoundedWeakLimit.exists_limit FN μ (NativeClock.rate*H) W hcW hW
    (fun k ↦ amplitude_holder ha hβ ell cap hell hb k) hβ hβ1
    (bound cap) (amplitude_bound ha hβ ell cap hell hb) R q
    (mul_pos NativeClock.rate_pos hpos) (PredictableTimeDilation.containsNullSets F _ μ hnull)
    Z (hZ₀.mono (F.le 0)).measurable hi he (root_holder ha hβ ell cap hell hb) (root_bound ell cap hb)
    (error (C := C) (β := β) ell) (error_nonneg ell) (error_tendsto hβ ell)
    (close ha hβ ell cap hell hb)

include P e b in
/-- The same construction supplies an initial-law-specific Borel
continuation kernel, including conditional native equations and full
Brownian histories, without a global choice of solutions. -/
theorem exists_kernel (hpos : 0 < H)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (Z : Ω → RealL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := η) (horizon H)),
      Q.toMeasure.map (NativeApproximationInitialLaw.initial (horizon H)) =
        μ.map (fun sample ↦ (Z sample, fun _ : η ↦ (0 : ℝ))) ∧
      GlobalNativeFourierLimitKernel.Supports (horizon H) (mul_pos NativeClock.rate_pos hpos) Q.toMeasure (root_holder ha hβ ell cap hell hb)
        hβ hβ1 (bound cap) (root_bound ell cap hb) q := by
  obtain ⟨W, hcW, hW, R, hi, he⟩ := GlobalNativeSmoothApproximationFamily.exists_family F μ H P e b q
    ha hβ hβ1 ell cap hell hb hpos hnull Z hZ₀ hZ
  let FN := PredictableTimeDilation.filtration F
    (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)
  exact GlobalNativeBoundedContinuationKernel.exists_kernel FN μ (NativeClock.rate*H) W hcW hW
    (fun k ↦ amplitude_holder ha hβ ell cap hell hb k) hβ hβ1
    (bound cap) (amplitude_bound ha hβ ell cap hell hb) R q
    (mul_pos NativeClock.rate_pos hpos) (PredictableTimeDilation.containsNullSets F _ μ hnull)
    Z (hZ₀.mono (F.le 0)).measurable hi he (root_holder ha hβ ell cap hell hb) (root_bound ell cap hb)
    (error (C := C) (β := β) ell) (error_nonneg ell) (error_tendsto hβ ell)
    (close ha hβ ell cap hell hb)

end SHEStochastic.GlobalNativePositiveWeakExistence
