module

public import SHE.CutoffWordHistories
public import SHE.CanonicalCovariance
public import SHE.TotalProfileParameters

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual canonical scalar profiles initialize the recursive physical
word construction. Parameters here describe TOTAL variances. For an
additive decomposition use TotalProfileParameters.add on the residual
parameters first; the total variance is then m²+a and the canonical
total profile is the proved reference used by the word covariance. -/
noncomputable section
namespace SHE.CanonicalCutoffWords
open Set MeasureTheory StoppedFourier WordRecursion
open CanonicalCovariance CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]

def referenceData (A : ProfileParameters) (ha : BoundedSmooth A.coefficient)
    (q : ℝ) (hq : 0 ≤ q) (u : CircleL2) : ReferenceData where
  totalVariance := A.coefficient
  totalVariance_smooth := ha
  reference := fun p => A.field q (u,p)
  reference_measurable := (A.field_measurable q).comp (measurable_const.prodMk measurable_id)
  upper := A.upper
  upper_nonneg := A.upper_nonneg
  reference_bound := fun p => by
    rw [abs_of_nonneg (A.lower_pos.le.trans (A.field_bounds q (u,p)).1)]
    exact (A.field_bounds q (u,p)).2
  reference_nonneg := fun p => A.lower_pos.le.trans (A.field_bounds q (u,p)).1
  base := q
  horizon := q+A.horizon
  base_nonneg := hq
  ordered := le_add_of_nonneg_right A.horizon_pos.le

def initialLevel (A : ProfileParameters) (ha : BoundedSmooth A.coefficient)
    (q : ℝ) (hq : 0 ≤ q) (u : CircleL2) {n : ℕ} (Z : Fin n → Observation)
    (s : ℝ) (hqs : q ≤ s) (hs : s ≤ q+A.horizon)
    (hZ : ∀ i, s ≤ (Z i).target) (hstop : ∀ i, s ≤ (Z i).stop)
    {F : WordRecursion.State n → ℝ} (hF : BoundedSmooth F) : Level (referenceData A ha q hq u) Unit n where
  observations := VariableObservations.Family.fixed Z
  terminal := fun _ => s
  terminal_measurable := measurable_const
  terminal_base := fun _ => hqs
  terminal_horizon := fun _ => hs
  targets_after := fun _ => hZ
  stops_after := fun _ => hstop
  test := fun _ => F
  test_uniform := UniformBoundedSmooth.fixed hF
  test_measurable := hF.smooth.continuous.measurable.comp measurable_snd

theorem initial_window_eq (A : ProfileParameters) (ha : BoundedSmooth A.coefficient)
    (q : ℝ) (hq : 0 ≤ q) (u : CircleL2) {n : ℕ} (Z : Fin n → Observation)
    (s : ℝ) (hqs : q ≤ s) (hs : s ≤ q+A.horizon)
    (hZ : ∀ i, s ≤ (Z i).target) (hstop : ∀ i, s ≤ (Z i).stop)
    {F : WordRecursion.State n → ℝ} (hF : BoundedSmooth F) :
    (initialLevel A ha q hq u Z s hqs hs hZ hstop hF).window () = A.window u q s Z hqs hZ := rfl

end SHE.CanonicalCutoffWords
