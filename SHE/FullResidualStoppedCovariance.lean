module

public import SHE.FullResidualChainCovariance
public import SHE.CoveredOldResidualCovariance
public import SHE.ObservationOldTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution CoveredHistoryGeometry CoveredControlledLaw
open scoped BigOperators
local instance fullResidualStoppedCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- A sum of original old intervals all lying after q is unchanged by
restricting its coefficient to the q-future window. -/
theorem old_sum_window {r : ℕ} (c : Domain→ℝ) (lo hi : Fin r→ℝ)
    {q : ℝ} (hlo : ∀ j,q≤lo j) :
    FutureWindowDomination.profile (sumProfile c lo hi) q=sumProfile c lo hi := by
  funext p
  by_cases hp : p∈FutureWindowDomination.timeSet q
  · exact Set.indicator_of_mem hp _
  · rw [FutureWindowDomination.profile,Set.indicator_of_notMem hp]
    symm
    apply Finset.sum_eq_zero
    intro j _
    apply Set.indicator_of_notMem
    intro hm
    exact hp ⟨(hlo j).trans hm.1.1.le,mem_univ _⟩

/-- Literal full-residual covariance at an arbitrary conditional base:
the original covered stopped history with reference minus the SAME
fixed old intervals. This is not a smaller common-front covariance. -/
theorem full_residual_eq_stopped_of_chain (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    {k : ℕ} {p : History X k} (chain : Chain L k p (fun i=>i))
    (hp : Physical L ((carrier L k).observations.observations p) c chain)
    (hZ : ∀ i,((carrier L k).observations.observations p i).stop≤
      ((carrier L k).observations.observations p i).target)
    (q : ℝ) (hq : 0≤q) (hqt : q≤(carrier L k).terminal p) :
    fullResidualCovariance L c k p q=
    stoppedCovariance (stops L k p) (targets L k p) (centers L k p)
      (fun z=>R.reference z-sumProfile c (lower L k p) (upper L k p) z) q := by
  have hgeom (i : Fin (n+k)) : stops L k p i≤targets L k p i:=
    (min_le_left _ _).trans (hZ i)
  have hcn (z : Domain) : 0≤c z ∧ c z≤R.upper:=
    ⟨hell.le.trans (hb z).1,(hb z).2.trans ((le_abs_self _).trans (R.reference_bound z))⟩
  have hca (z : Domain) : |c z|≤R.upper:=by
    rw [abs_of_nonneg (hcn z).1]
    exact (hcn z).2
  have hold (z : Domain) : |sumProfile c (lower L k p) (upper L k p) z|≤R.upper := by
    have hh:=sumProfile_bounds c (fun z=>(hcn z).1) (lower L k p) (upper L k p) (disjoint L k p) z
    rw [abs_of_nonneg hh.1]
    exact hh.2.trans (hcn z).2
  have hsum : (∑ j,covariances L ((carrier L k).observations.observations p) c k p j)=
      stoppedCovariance (stops L k p) (targets L k p) (centers L k p)
        (sumProfile c (lower L k p) (upper L k p)) q := by
    rw [←CoveredControlledLaw.old_family_eq L c k p hq hqt,
      ←covariance_sumProfile _ _ _ hgeom c hc R.upper_nonneg hca]
    rw [←FutureWindowDomination.covariance_eq _ _ _ _ hq,
      old_sum_window c (lower L k p) (upper L k p)
        (fun j=>hqt.trans (terminal_le_lower L k p j))]
  have he:=StoppedCovarianceSplit.covariance_sub (stops L k p) (targets L k p) (centers L k p) hgeom q R.reference_measurable
    (measurable_sumProfile hc _ _) R.reference_bound hold
  rw [he]
  apply (eq_sub_iff_add_eq).mpr
  have hf:=full_residual_add_old_of_chain L c hc hell hb chain hp hZ q hq hqt
  rw [hsum] at hf
  exact (add_comm _ _).trans hf

end SHE.PhysicalChainArrays
