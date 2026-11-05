module

public import SHE.ControlledObservationTransfer
public import SHE.PhysicalMeanSemigroup

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFutureMeans
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures StoppedGaussianScore
  GaussianIncrement ControlledProfile PhysicalProfile PhysicalMeanRange PhysicalMeanSemigroup
open scoped InnerProductSpace
local instance controlledFutureMeans_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def referenceState (Λ q : ℝ) (hq : 0 ≤ q) (u d : CircleL2) (θ : ℝ) : CircleL2 :=
  circleHeatOperator q hq u + (θ * exp (-Λ * q)) • circleHeatOperator q hq d

/-- The actual conditional future mean, retaining the current interpolated
state and the compensated controlled reference mean. -/
def futureMeanVector (Λ : ℝ) (target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (u d Z D : CircleL2) (θ : ℝ) : State n :=
  WithLp.toLp 2 (fun i =>
    physicalHeatMean (Z + θ • D) (target i - q, nativeCenter a i) +
      mean Λ u d (θ, (target i, nativeCenter a i)) -
        physicalHeatMean (referenceState Λ q hq u d θ) (target i - q, nativeCenter a i))

/-- Both the actual current input and the old remaining-mean correction
are kept. The damping is evaluated at the original observation age. -/
def futureDirection (Λ : ℝ) (target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (d D : CircleL2) : State n :=
  currentDirection target a q D + exp (-Λ * q) •
    (dampedDirection target target a q Λ (circleHeatOperator q hq d) -
      currentDirection target a q (circleHeatOperator q hq d))

theorem futureMeanVector_affine (Λ : ℝ) (target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (hgap : ∀ i, q < target i) (u d Z D : CircleL2) (θ : ℝ) :
    futureMeanVector Λ target a q hq u d Z D θ =
      currentDirection target a q Z + θ • futureDirection Λ target a q hq d D := by
  apply PiLp.ext
  intro i
  have hr : 0 < target i - q := sub_pos.mpr (hgap i)
  have hT : 0 < target i := lt_of_le_of_lt hq (hgap i)
  have htime : q + (target i - q) = target i := by ring
  have he : exp (-Λ * q) * exp (-Λ * (target i - q)) = exp (-Λ * target i) := by
    rw [← exp_add]
    congr 1
    ring
  change physicalHeatMean (Z + θ • D) (target i - q, nativeCenter a i) +
      (physicalHeatMean u (target i, nativeCenter a i) +
        θ * exp (-Λ * target i) * physicalHeatMean d (target i, nativeCenter a i)) -
      physicalHeatMean (circleHeatOperator q hq u + (θ * exp (-Λ * q)) • circleHeatOperator q hq d)
        (target i - q, nativeCenter a i) =
    physicalHeatMean Z (target i - q, nativeCenter a i) + θ *
      (physicalHeatMean D (target i - q, nativeCenter a i) + exp (-Λ * q) *
        (exp (-Λ * (target i - q)) * physicalHeatMean (circleHeatOperator q hq d) (target i - q, nativeCenter a i) -
          physicalHeatMean (circleHeatOperator q hq d) (target i - q, nativeCenter a i)))
  rw [heatMean_add hr, heatMean_smul hr, heatMean_add hr, heatMean_smul hr,
    heatMean_heat hr hq, heatMean_heat hr hq, htime]
  rw [← he]
  ring

/-- The genuine current-plus-old mean direction belongs to the full
future covariance range. The current state may be completely arbitrary. -/
theorem futureDirection_mem_range (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ) (hq : 0 ≤ q)
    (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, q + δ ≤ target i)
    (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 < ell) (hcl : ∀ p, ell ≤ c p)
    (d D : CircleL2) :
    futureDirection Λ target a q hq d D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance target target (nativeCenter a) c q)).range := by
  have hcur := currentDirection_mem_range target target a q (fun _ => le_rfl) δ hδ hstop c hc U ell hcb hell hcl D
  have hold := currentDirection_mem_range target target a q (fun _ => le_rfl) δ hδ hstop c hc U ell hcb hell hcl
    (circleHeatOperator q hq d)
  have hdamp := dampedDirection_mem_range target target a q Λ hΛ (fun _ => le_rfl) δ hδ hstop c hc U ell hcb hell hcl
    (circleHeatOperator q hq d)
  exact Submodule.add_mem _ hcur (Submodule.smul_mem _ _ (Submodule.sub_mem _ hdamp hold))

end SHE.ControlledFutureMeans
