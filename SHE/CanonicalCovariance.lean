module

public import SHE.CovarianceFamilies
public import SHE.CanonicalProfile

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual canonical Picard profile supplies a Borel family of physical
observation covariances and backward Gaussian tests. -/
noncomputable section
namespace SHE.CanonicalCovariance
open Set MeasureTheory ProbabilityTheory StoppedFourier
open CovarianceEndpoint CovarianceFamilies GaussianContinuity GaussianConvolution GaussianItoTest
open scoped Matrix.Norms.Elementwise

abbrev State (n : ℕ) := WordRecursion.State n

structure ProfileParameters where
  coefficient : ℝ → ℝ
  lower : ℝ
  upper : ℝ
  holder : ℝ
  exponent : ℝ
  horizon : ℝ
  measurable : Measurable coefficient
  lower_pos : 0 < lower
  upper_nonneg : 0 ≤ upper
  holder_nonneg : 0 ≤ holder
  exponent_pos : 0 < exponent
  exponent_le_one : exponent ≤ 1
  horizon_pos : 0 < horizon
  horizon_le_one : horizon ≤ 1
  lower_bound : ∀ z, lower ≤ coefficient z
  upper_bound : ∀ z, coefficient z ≤ upper
  holder_bound : ∀ z w, |coefficient z - coefficient w| ≤ holder * |z - w| ^ exponent
  small : GaussianProfile.contractionConstant lower holder exponent * horizon ^ (exponent / 4) ≤ 1 / 2

variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]

namespace ProfileParameters
variable (P : ProfileParameters)

def field (q : ℝ) (p : CircleL2 × (ℝ × HeatCircle)) : ℝ :=
  CanonicalProfile.profile P.coefficient P.lower P.horizon (p.1, (p.2.1 - q, p.2.2))

theorem field_measurable (q : ℝ) : Measurable (P.field q) := by
  have hm := CanonicalProfile.profile_measurable P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
    P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
    P.holder_bound P.small
  exact hm.comp ((measurable_fst).prodMk ((measurable_snd.fst.sub_const q).prodMk measurable_snd.snd))

theorem field_bounds (q : ℝ) (p : CircleL2 × (ℝ × HeatCircle)) :
    P.lower ≤ P.field q p ∧ P.field q p ≤ P.upper :=
  CanonicalProfile.profile_elliptic P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
    P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
    P.holder_bound P.small _

def window {n : ℕ} (u : CircleL2) (q s : ℝ) (Z : Fin n → WordRecursion.Observation)
    (hqs : q ≤ s) (hZ : ∀ i, s ≤ (Z i).target) : EndpointWindow n where
  coefficient := fun p => P.field q (u, p)
  measurable := (P.field_measurable q).comp (measurable_const.prodMk measurable_id)
  observations := Z
  left := q
  right := s
  upper := P.upper
  ordered := hqs
  upper_nonneg := P.upper_nonneg
  target_after := hZ
  bounded := fun t _ x => by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.field_bounds q (u, (t, x))).1)]
    exact (P.field_bounds q (u, (t, x))).2
  nonneg := fun t _ x => P.lower_pos.le.trans (P.field_bounds q (u, (t, x))).1

theorem path_measurable {n : ℕ} (q s : ℝ) (Z : Fin n → WordRecursion.Observation)
    (hqs : q ≤ s) (hZ : ∀ i, s ≤ (Z i).target) :
    Measurable (fun p : CircleL2 × ℝ => (P.window p.1 q s Z hqs hZ).path p.2) := by
  exact positive_clipped_covariance_measurable (P.field_measurable q) Z hqs
    (fun p => ((P.window p.1 q s Z hqs hZ).path p.2).property)

/-- Joint Borel dependence on the actual initial L² input, time, and finite
observation state. This is the selection needed before conditioning on a
random past input. -/
theorem backward_measurable {n : ℕ} (q s : ℝ) (Z : Fin n → WordRecursion.Observation)
    (hqs : q ≤ s) (hZ : ∀ i, s ≤ (Z i).target) {F : State n → ℝ}
    (hF : Continuous F) {M : ℝ} (hbound : ∀ z, ‖F z‖ ≤ M) :
    Measurable (fun p : (CircleL2 × ℝ) × State n =>
      backward (P.window p.1.1 q s Z hqs hZ) F p.1.2 p.2) :=
  gaussian_family_measurable (P.path_measurable q s Z hqs hZ) hF hbound

theorem random_backward_measurable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → CircleL2} (hU : Measurable U) (q s : ℝ) (Z : Fin n → WordRecursion.Observation)
    (hqs : q ≤ s) (hZ : ∀ i, s ≤ (Z i).target) {F : State n → ℝ}
    (hF : Continuous F) {M : ℝ} (hbound : ∀ z, ‖F z‖ ≤ M) :
    Measurable (fun p : (Ω × ℝ) × State n =>
      backward (P.window (U p.1.1) q s Z hqs hZ) F p.1.2 p.2) := by
  have hmap : Measurable (fun p : (Ω × ℝ) × State n => ((U p.1.1, p.1.2), p.2)) :=
    (((hU.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd)
  have hm := (P.backward_measurable q s Z hqs hZ hF hbound).comp hmap
  exact hm

end ProfileParameters
end SHE.CanonicalCovariance
