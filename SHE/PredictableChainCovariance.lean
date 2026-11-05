module

public import SHE.StoppedWindowCovariance
public import SHE.ActualPredictableScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers ProjectedUncutWord StoppedGaussianFeatures GaussianConvolution
open scoped BigOperators
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def initialCovariance (k : ℕ) (p : History P k) : MeasurableGeneralizedInverse.Mat (n+k) :=
  ((carrier L k).nodeCovariance (p,(R.base,0))).val

/-- The complete predictable Gaussian window uses the actual conditional
lower cutoff and clips original stops at the original word horizon.
Original heat targets are left unchanged. -/
def windowCovariance (k : ℕ) (p : History P k) : MeasurableGeneralizedInverse.Mat (n+k) :=
  StoppedGaussianFeatures.stoppedCovariance
    (fun i => min ((carrier L k).observations.observations p i).stop (initialTerminal L k p))
    (fun i => ((carrier L k).observations.observations p i).target)
    (fun i => ((carrier L k).observations.observations p i).center) R.reference R.base

theorem initialCovariance_interval (k : ℕ) (p : History P k)
    (hZ : ∀ i, ((carrier L k).observations.observations p i).stop ≤
      ((carrier L k).observations.observations p i).target) :
    initialCovariance L k p = intervalCovariance ((carrier L k).observations.observations p)
      R.reference R.base ((carrier L k).terminal p) := by
  have ht : (carrier L k).nodeTime (p,(R.base,0)) = R.base :=
    ClippedCovariance.clip_eq ⟨le_rfl,(carrier L k).terminal_base p⟩
  change WordRecursion.covariance R.reference ((carrier L k).observations.observations p)
    ((carrier L k).nodeTime (p,(R.base,0))) ((carrier L k).terminal p) = _
  rw [ht]
  exact (PhysicalIntervalCovariance.interval_eq_covariance _ R.reference R.reference_measurable
    R.reference_bound hZ ((carrier L k).stops_after p) R.base_nonneg
    ((carrier L k).terminal_base p)).symm

/-- Actual initial-to-newest covariance plus every original old/residual
interval is precisely the full conditional window covariance. No noise
before the conditional base or after the original horizon is added. -/
theorem Physical.predictable_covariance {k : ℕ} {p : History P k}
    (hZ : ∀ i, ((carrier L k).observations.observations p i).stop ≤
      ((carrier L k).observations.observations p i).target)
    (c : Domain → ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ z, ell ≤ c z ∧ c z ≤ R.reference z)
    (chain : Chain (N := n+k) L k p (fun i => i))
    (hp : Physical L ((carrier L k).observations.observations p) c chain) :
    initialCovariance L k p + (∑ j, (chain.old j + chain.residual j)) = windowCovariance L k p := by
  rw [initialCovariance_interval L k p hZ, Physical.sum_full L _ hZ c hc hell hb chain hp]
  rw [interval_add_adjacent _ hZ R.reference R.reference_measurable R.upper_nonneg R.reference_bound
    ((carrier L k).terminal_base p) (terminal_le_initial L k p)]
  exact StoppedWindowCovariance.interval_eq_clipped _ R.reference R.base_nonneg

/-- The varying reserved covariance is exactly the actual full window
covariance minus the fixed old covariance sum. -/
theorem Physical.residual_covariance {k : ℕ} {p : History P k}
    (hZ : ∀ i, ((carrier L k).observations.observations p i).stop ≤
      ((carrier L k).observations.observations p i).target)
    (c : Domain → ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ z, ell ≤ c z ∧ c z ≤ R.reference z)
    (chain : Chain (N := n+k) L k p (fun i => i))
    (hp : Physical L ((carrier L k).observations.observations p) c chain) :
    initialCovariance L k p + (∑ j, chain.residual j) =
      windowCovariance L k p - (∑ j, chain.old j) := by
  have h := hp.predictable_covariance L hZ c hc hell hb chain
  rw [Finset.sum_add_distrib] at h
  apply (eq_sub_iff_add_eq).mpr
  calc
    _ = initialCovariance L k p + ((∑ j, chain.old j) + ∑ j, chain.residual j) := by abel
    _ = _ := h

end SHE.PhysicalScoreChain
