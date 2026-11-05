module

public import SHE.ControlledFutureTransfer

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFutureFields
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures StoppedGaussianScore
  GaussianIncrement ControlledProfile PhysicalProfile PhysicalMeanRange PhysicalMeanSemigroup ControlledFutureMeans
open scoped InnerProductSpace
local instance controlledFutureFields_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def explicitDirection (Λ : ℝ) (target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (q : ℝ) (d D : CircleL2) : State n :=
  WithLp.toLp 2 (fun i => physicalHeatMean D (target i - q, nativeCenter a i) +
    (exp (-Λ * target i) - exp (-Λ * q)) * physicalHeatMean d (target i, nativeCenter a i))

theorem explicitDirection_eq (Λ : ℝ) (target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (hgap : ∀ i, q < target i) (d D : CircleL2) :
    explicitDirection Λ target a q d D = futureDirection Λ target a q hq d D := by
  apply PiLp.ext
  intro i
  have hr : 0 < target i - q := sub_pos.mpr (hgap i)
  have htime : q + (target i - q) = target i := by ring
  have he : exp (-Λ * q) * exp (-Λ * (target i - q)) = exp (-Λ * target i) := by
    rw [← exp_add]
    congr 1
    ring
  change physicalHeatMean D (target i - q, nativeCenter a i) +
      (exp (-Λ * target i) - exp (-Λ * q)) * physicalHeatMean d (target i, nativeCenter a i) =
    physicalHeatMean D (target i - q, nativeCenter a i) + exp (-Λ * q) *
      (exp (-Λ * (target i - q)) * physicalHeatMean (circleHeatOperator q hq d) (target i - q, nativeCenter a i) -
        physicalHeatMean (circleHeatOperator q hq d) (target i - q, nativeCenter a i))
  rw [heatMean_heat hr hq, htime, ← he]
  ring

variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {X : Type*} [MeasurableSpace X]

/-- Actual future-direction substitution is jointly Borel in both physical
inputs, times and relative centers. All these data may be dependent. -/
theorem explicitDirection_measurable (Λ : ℝ) (target : X → Fin n → ℝ)
    (hT : ∀ i, Measurable (fun x => target x i)) (a : X → Fin n → UnitAddCircle)
    (ha : ∀ i, Measurable (fun x => a x i)) (q : X → ℝ) (hq : Measurable q)
    (d D : X → CircleL2) (hd : Measurable d) (hD : Measurable D) :
    Measurable (fun x => explicitDirection Λ (target x) (a x) (q x) (d x) (D x)) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hc := (CircleNormalization.continuous_scale 1 (2 * π)).measurable.comp (ha i)
  have hcur := physicalHeatMean_joint_measurable.comp (hD.prodMk (((hT i).sub hq).prodMk hc))
  have hold := physicalHeatMean_joint_measurable.comp (hd.prodMk ((hT i).prodMk hc))
  exact hcur.add (((((hT i).const_mul (-Λ)).exp).sub ((hq.const_mul (-Λ)).exp)).mul hold)

theorem futureDirection_measurable (Λ : ℝ) (target : X → Fin n → ℝ)
    (hT : ∀ i, Measurable (fun x => target x i)) (a : X → Fin n → UnitAddCircle)
    (ha : ∀ i, Measurable (fun x => a x i)) (q : X → ℝ) (hq : Measurable q)
    (hq0 : ∀ x, 0 ≤ q x) (hgap : ∀ x i, q x < target x i)
    (d D : X → CircleL2) (hd : Measurable d) (hD : Measurable D) :
    Measurable (fun x => futureDirection Λ (target x) (a x) (q x) (hq0 x) (d x) (D x)) := by
  have he : (fun x => explicitDirection Λ (target x) (a x) (q x) (d x) (D x)) =
      fun x => futureDirection Λ (target x) (a x) (q x) (hq0 x) (d x) (D x) := by
    funext x
    exact explicitDirection_eq Λ (target x) (a x) (q x) (hq0 x) (hgap x) (d x) (D x)
  rw [← he]
  exact explicitDirection_measurable Λ target hT a ha q hq d D hd hD

/-- The literal compensated Gaussian future mean is jointly Borel in
arbitrary dependent current states, old inputs, times and centers. -/
theorem futureMeanVector_measurable (Λ : ℝ) (target : X → Fin n → ℝ)
    (hT : ∀ i, Measurable (fun x => target x i)) (a : X → Fin n → UnitAddCircle)
    (ha : ∀ i, Measurable (fun x => a x i)) (q : X → ℝ) (hq : Measurable q)
    (hq0 : ∀ x, 0 ≤ q x) (hgap : ∀ x i, q x < target x i)
    (u d Z D : X → CircleL2) (hd : Measurable d) (hZ : Measurable Z) (hD : Measurable D)
    (θ : X → ℝ) (hθ : Measurable θ) :
    Measurable (fun x => futureMeanVector Λ (target x) (a x) (q x) (hq0 x) (u x) (d x) (Z x) (D x) (θ x)) := by
  have hcur : Measurable (fun x => currentDirection (target x) (a x) (q x) (Z x)) := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply Measurable.of_eval
    intro i
    exact physicalHeatMean_joint_measurable.comp (hZ.prodMk (((hT i).sub hq).prodMk
      ((CircleNormalization.continuous_scale 1 (2 * π)).measurable.comp (ha i))))
  have hm := hcur.add (hθ.smul (futureDirection_measurable Λ target hT a ha q hq hq0 hgap d D hd hD))
  change Measurable (fun x => currentDirection (target x) (a x) (q x) (Z x) +
    θ x • futureDirection Λ (target x) (a x) (q x) (hq0 x) (d x) (D x)) at hm
  have he (x : X) := futureMeanVector_affine Λ (target x) (a x) (q x) (hq0 x) (hgap x)
    (u x) (d x) (Z x) (D x) (θ x)
  simpa only [← he] using hm

end SHE.ControlledFutureFields
