module

public import SHEStochastic.JointFourierCylinderGenerator
public import SHEStochastic.WeakLimitCylinderMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.JointFourierWeakLimit
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open GaussianItoTest StoppedPathPasting
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [Countable ι]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B)
  {Gn : ℕ → ℝ → V} {Cn : ℕ → ℝ≥0}
  (hGn : ∀ k, HolderWith (Cn k) β (Gn k)) (hbn : ∀ k z, ‖Gn k z‖ ≤ B)
  {s d : ℕ} (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ)
  (b : Fin d → Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (driver : Fin d → ι)
  (f : State (s + d) → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)

/-- Weak joint limits preserve the full state/driver cylinder problem
under uniform coefficient approximation. Mixed brackets are retained,
rather than identifying only the marginal state covariance. -/
theorem identity (H : ℝ≥0) (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (hδlim : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k z, ‖G z - Gn k z‖ ≤ δ k)
    (P : ℕ → ProbabilityMeasure (Path H (RealL2 × (ι → ℝ))))
    (Q : ProbabilityMeasure (Path H (RealL2 × (ι → ℝ)))) (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ k, PastedCylinderMartingale.Identity H
      (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.generator (hGn k) hβ hβ1 B hB (hbn k) a n b driver f hf hs)
      (P k : Measure (Path H (RealL2 × (ι → ℝ))))) :
    PastedCylinderMartingale.Identity H (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.generator hG hβ hβ1 B hB hb a n b driver f hf hs)
      (Q : Measure (Path H (RealL2 × (ι → ℝ)))) :=
  WeakLimitCylinderMartingale.identity_of_generator_limit H _ _ _ P Q hlim
    (JointFourierCylinderGenerator.uniform_generator_limit hG hβ hβ1 B hB hb a n b driver f hf hs
      hGn hbn δ hδ hδlim hclose) hP

end SHEStochastic.JointFourierWeakLimit
