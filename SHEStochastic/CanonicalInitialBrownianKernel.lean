module

public import SHEStochastic.CanonicalInitialKernel
public import SHEStochastic.CanonicalBrownianSubGaussian
public import SHE.CanonicalConditionalBrownianLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.CanonicalInitialBrownianKernel
open MeasureTheory ProbabilityTheory SHE SHE.DyadicApproximation SHE.FiniteHaar
open CanonicalStateDriverFiltration CanonicalInitialKernel
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0)
  (Q : Measure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H)) [IsProbabilityMeasure Q]
  (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn (filtration H) Q H
    (fun i ↦ coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0))

include hBrown in
theorem zero (i : ι) : coordinate H i 0 =ᵐ[Q] fun _ ↦ (0 : ℝ) :=
  by
    let P : FiniteScalarIto.Family (filtration (E := E) (ι := ι) H) Q H ι :=
      ⟨⟨coordinate H,coordinate_adapted H,hBrown⟩,coordinate_continuous H⟩
    exact FiniteScalarIto.zero_ae P.toCoordinates i


include hBrown in
theorem bundle_ae_id : CanonicalFutureStateDriver.bundle (state H) (state_continuous H)
    (coordinate H) (coordinate_continuous H) 0 H =ᵐ[Q] id := by
  have hc (t : Set.Icc (0 : ℝ) (H : ℝ)) : clock H t.val.toNNReal = t := by
    apply Subtype.ext
    change min ((t.val.toNNReal : ℝ≥0) : ℝ) (H : ℝ) = t.val
    rw [Real.coe_toNNReal _ t.property.1, min_eq_left t.property.2]
  filter_upwards [ae_all_iff.mpr (zero H Q hBrown)] with x hx
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change x.1 (clock H (0+t.val.toNNReal)) = x.1 t
    rw [zero_add, hc]
  · funext i
    apply ContinuousMap.ext
    intro t
    change coordinate H i (0+t.val.toNNReal) x-coordinate H i 0 x = x.2 i t
    rw [zero_add, hx i, sub_zero]
    change x.2 i (clock H t.val.toNNReal) = x.2 i t
    rw [hc]

include hBrown in
/-- Conditioning the one constructed joint law at its initial state
retains Brownian motion in the ENTIRE canonical state-and-driver past. -/
theorem law : ∀ᵐ z ∂initialLaw H Q, ∀ d (a : Fin d → ι),
    FiniteBrownianLawOn (filtration (E := E) (ι := ι) H) (kernel H Q z) H
      (fun i ↦ coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0) := by
  have hh := CanonicalConditionalBrownianLaw.law (filtration H) Q H
    (state H) (state_continuous H) (coordinate H) (coordinate_continuous H)
    (state_adapted H) (coordinate_adapted H) hBrown 0 H (by rw [zero_add])
    (state H 0) (state_adapted H 0)
  have hk : condDistrib (CanonicalFutureStateDriver.bundle (state H) (state_continuous H)
      (coordinate H) (coordinate_continuous H) 0 H) (state H 0) Q = kernel H Q :=
    condDistrib_congr_left (bundle_ae_id H Q hBrown)
  rw [hk] at hh
  exact hh

include hBrown in
/-- Driver moments are uniform for every Hilbert state space. -/
theorem subgaussian (i : ι) (t : ℝ≥0) :
    HasSubgaussianMGF (coordinate (E := E) H i t) (min t H) Q := by
  have hl := BrownianCoordinates.eval_law (filtration H) Q H (coordinate H) hBrown
    i (min t H) (min_le_right _ _)
  have he : coordinate (E := E) H i (min t H)=coordinate H i t := by
    funext x
    simp [coordinate,clock,NNReal.coe_min,min_assoc,min_self]
  rw [he] at hl
  exact CanonicalBrownianSubGaussian.of_law Q (min t H) hl

end SHEStochastic.CanonicalInitialBrownianKernel

