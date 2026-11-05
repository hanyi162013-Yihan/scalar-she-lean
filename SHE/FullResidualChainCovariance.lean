module

public import SHE.FullResidualChainAverage
public import SHE.CoveredControlledCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution
open scoped BigOperators
local instance fullResidualChainCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- The old covariance sum plus the ACTUAL full residual is exactly the
covered stopped covariance, at any original conditional base. Each
original target is retained and stops are clipped only at the original
root horizon. A canonical common-chain event discharges the chain below. -/
theorem full_residual_add_old_of_chain (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    {k : ℕ} {p : History X k} (chain : Chain L k p (fun i=>i))
    (hp : Physical L ((carrier L k).observations.observations p) c chain)
    (hZ : ∀ i,((carrier L k).observations.observations p i).stop≤
      ((carrier L k).observations.observations p i).target)
    (q : ℝ) (hq : 0≤q) (hqt : q≤(carrier L k).terminal p) :
    (∑ j,covariances L ((carrier L k).observations.observations p) c k p j)+
      fullResidualCovariance L c k p q=
    stoppedCovariance (fun i=>min ((carrier L k).observations.observations p i).stop (initialTerminal L k p))
      (fun i=>((carrier L k).observations.observations p i).target)
      (fun i=>((carrier L k).observations.observations p i).center) R.reference q := by
  let Z:=(carrier L k).observations.observations p
  let T:=(carrier L k).terminal p
  have hs:=Physical.sum_full L Z hZ c hc hell hb chain hp
  rw [Physical.old_eq L Z c chain hp,Physical.residual_eq L Z c chain hp] at hs
  have hfront:=PhysicalIntervalCovariance.interval_eq_covariance Z R.reference R.reference_measurable
    R.reference_bound hZ ((carrier L k).stops_after p) hq hqt
  calc
    _ = intervalCovariance Z R.reference q T+
        ∑ j,(covariances L Z c k p j+covariances L Z (fun r=>R.reference r-c r) k p j) := by
      unfold fullResidualCovariance
      rw [←hfront]
      change (∑ j,covariances L Z c k p j)+(intervalCovariance Z R.reference q T+
        ∑ j,covariances L Z (fun r=>R.reference r-c r) k p j)=_
      rw [Finset.sum_add_distrib]
      abel
    _ = intervalCovariance Z R.reference q T+
        intervalCovariance Z R.reference T (initialTerminal L k p) := by rw [hs]
    _ = intervalCovariance Z R.reference q (initialTerminal L k p) :=
      interval_add_adjacent Z hZ R.reference R.reference_measurable R.upper_nonneg R.reference_bound
        hqt (terminal_le_initial L k p)
    _ = _ := StoppedWindowCovariance.interval_eq_clipped Z R.reference hq

end SHE.PhysicalChainArrays
