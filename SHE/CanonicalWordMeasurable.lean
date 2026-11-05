module

public import SHE.CanonicalCovariance
public import SHE.ObservationMeasurable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Joint Borel realization of the actual space-time operator insertion,
including canonical reference profiles selected by a past L² input. -/
noncomputable section
namespace SHE.CanonicalWordMeasurable
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion GaussianItoTest PhysicalIto CovarianceFamilies CanonicalCovariance ObservationMeasurable

abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type*} [MeasurableSpace P]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]

def familyRemainder {n : ℕ} (a : ℝ → ℝ) (c : P × (ℝ × HeatCircle) → ℝ)
    (Z : Fin n → Observation) (G : P → ℝ → State n → ℝ)
    (U : P × ℝ → CircleL2) (X : P × (ℝ × HeatCircle) → ℝ) (q s : ℝ) (p : P) : ℝ :=
  ∫ t in q..s, ∫ x : HeatCircle,
    insertion a (fun r => c (p, r)) Z t x (G p t)
      (observe (fun r => U (p, r)) (fun r => X (p, r)) (appendObservation Z t x) t) ∂AddCircle.haarAddCircle

theorem familyRemainder_measurable {n : ℕ} (Z : Fin n → Observation)
    {U : P × ℝ → CircleL2} (hU : Measurable U) {X : P × (ℝ × HeatCircle) → ℝ} (hX : Measurable X)
    {a : ℝ → ℝ} (ha : Measurable a) {c : P × (ℝ × HeatCircle) → ℝ} (hc : Measurable c)
    (G : P → ℝ → State n → ℝ)
    (hH : Measurable (fun p : (P × ℝ) × State n => GaussianTaylor.hessian (G p.1.1 p.1.2) p.2))
    {q s : ℝ} (hqs : q ≤ s) : Measurable (familyRemainder a c Z G U X q s) := by
  have hi := inserted_field_measurable Z hU hX ha hc G hH
  have hx := hi.stronglyMeasurable.integral_prod_right' (ν := AddCircle.haarAddCircle)
  have ht := hx.integral_prod_right' (ν := volume.restrict (Ioc q s))
  convert ht.measurable using 1
  funext p
  unfold familyRemainder
  exact intervalIntegral.integral_of_le hqs

theorem canonical_hessian_measurable (A : ProfileParameters) {n : ℕ} (q s : ℝ)
    (Z : Fin n → Observation) (hqs : q ≤ s) (hZ : ∀ i, s ≤ (Z i).target)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) :
    Measurable (fun p : (CircleL2 × ℝ) × State n =>
      GaussianTaylor.hessian (backward (A.window p.1.1 q s Z hqs hZ) F p.1.2) p.2) :=
  gaussian_hessian_family_measurable (A.path_measurable q s Z hqs hZ) hF hbound hD hDD

/-- The reference selected by a random initial input and the literal
physical insertion remainder are a single jointly Borel object. -/
theorem canonical_remainder_measurable (A : ProfileParameters) {n : ℕ} (q s : ℝ)
    (Z : Fin n → Observation) (hqs : q ≤ s) (hZ : ∀ i, s ≤ (Z i).target)
    {u : P → CircleL2} (hu : Measurable u)
    {U : P × ℝ → CircleL2} (hU : Measurable U) {X : P × (ℝ × HeatCircle) → ℝ} (hX : Measurable X)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) :
    Measurable (fun p : P => wordRemainder (A.window (u p) q s Z hqs hZ) A.coefficient
      (fun t => U (p, t)) (fun r => X (p, r)) F) := by
  have hc : Measurable (fun p : P × (ℝ × HeatCircle) => A.field q (u p.1, p.2)) :=
    (A.field_measurable q).comp ((hu.comp measurable_fst).prodMk measurable_snd)
  have hmap : Measurable (fun p : (P × ℝ) × State n => ((u p.1.1, p.1.2), p.2)) :=
    (((hu.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd)
  have hh := (canonical_hessian_measurable A q s Z hqs hZ hF hbound hD hDD).comp hmap
  have hr := familyRemainder_measurable Z hU hX A.measurable hc
    (fun p t => backward (A.window (u p) q s Z hqs hZ) F t) hh hqs
  convert hr using 1
  funext p
  rfl

end SHE.CanonicalWordMeasurable
