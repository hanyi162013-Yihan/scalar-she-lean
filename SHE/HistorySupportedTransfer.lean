module

public import SHE.HistoryGeometry
public import SHE.UniformOldIntervalScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.HistorySupportedTransfer
open Set MeasureTheory WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry StoppedGaussianFeatures StoppedFourier
  FixedOldScoreSupport GaussianIncrement
variable {X : Type} [MeasurableSpace X] {R R' : ReferenceData} {n : ℕ}
variable (L : Level R X n) (L' : Level R' X n)

/-- The old covariance depends solely on actual carrier geometry and
its coefficient; it does not depend on the reference data elsewhere. -/
theorem profileCovariances_eq
    (hterminal : ∀ k h,(carrier L k).terminal h=(carrier L' k).terminal h)
    (hnode : ∀ k h,(carrier L k).nodeTime h=(carrier L' k).nodeTime h)
    (hobs : ∀ k h,(carrier L k).observations.observations h=(carrier L' k).observations.observations h)
    (c : Domain→ℝ) (k : ℕ) (h : History X (k+1)) :
    profileCovariances L c k h=profileCovariances L' c k h := by
  unfold profileCovariances
  rw [hterminal k h.1,hnode k h,hobs k h.1]

/-- A local old row already represented by the constant floor remains
in range for EVERY actual bounded elliptic coefficient on that window. -/
theorem node_range_of_floor (c : Domain→ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0<ell)
    (hb : ∀ z,ell ≤ c z ∧ c z ≤ R'.reference z)
    (hages : ∀ x i,(L'.observations.observations x i).stop ≤ (L'.observations.observations x i).target)
    (k : ℕ) (h : History X (k+1))
    (hrange : row L' k h∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (profileCovariances L' (fun _=>ell) k h)).range) :
    row L' k h∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (profileCovariances L' c k h)).range := by
  let Z := (carrier L' k).observations.observations h.1
  let lo := (carrier L' k).nodeTime h
  let hi := (carrier L' k).terminal h.1
  have hZ := RecursiveScoreSupport.carrier_ages L' hages k h.1
  have hcb (p : Domain) : ell ≤ c p ∧ c p ≤ R'.upper :=
    ⟨(hb p).1,(hb p).2.trans ((le_abs_self _).trans (R'.reference_bound p))⟩
  have he (d : Domain→ℝ) (hd : Measurable d) (hdM : ∀ p,|d p| ≤ R'.upper) :
      intervalCovariance Z d lo hi=profileCovariances L' d k h :=
    PhysicalIntervalCovariance.interval_eq_covariance Z d hd hdM hZ ((carrier L' k).stops_after h.1)
      (R'.base_nonneg.trans ((carrier L' k).nodeTime_mem h).1) ((carrier L' k).nodeTime_mem h).2
  have hellUpper : ell ≤ R'.upper := (hb (0,0)).1.trans (hcb (0,0)).2
  have hzero := he (fun _=>ell) measurable_const (fun _=>by rw [abs_of_pos hell];exact hellUpper)
  have hfull := he c hc (fun p=>by rw [abs_of_nonneg (hell.le.trans (hb p).1)];exact (hcb p).2)
  rw [←hzero] at hrange
  rw [←hfull]
  exact (UniformOldIntervalScores.interval_range_and_score _ _ _ hZ lo hi c hc hell hcb _ hrange).1

/-- Transfer the actual recursive Gaussian applicability predicate from
ONE floor chain to a different reference with the same physical geometry.
Only the new coefficient/residual positivity is checked pointwise. -/
theorem supported_of_floor
    (hterminal : ∀ k h,(carrier L k).terminal h=(carrier L' k).terminal h)
    (hnode : ∀ k h,(carrier L k).nodeTime h=(carrier L' k).nodeTime h)
    (hobs : ∀ k h,(carrier L k).observations.observations h=(carrier L' k).observations.observations h)
    (hrow : ∀ k h,row L k h=row L' k h)
    (c : Domain→ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0<ell)
    (hb : ∀ z,ell ≤ c z ∧ c z ≤ R'.reference z)
    (hages : ∀ x i,(L'.observations.observations x i).stop ≤ (L'.observations.observations x i).target)
    (k : ℕ) (h : History X k)
    (hsup : RecursiveGaussianScores.Supported L (profileCovariances L (fun _=>ell))
      (profileCovariances L (fun p=>R.reference p-ell)) k h) :
    RecursiveGaussianScores.Supported L' (profileCovariances L' c)
      (profileCovariances L' (fun p=>R'.reference p-c p)) k h := by
  induction k with
  | zero => trivial
  | succ k ih =>
    have hcb (z : Domain) : 0 ≤ c z ∧ c z ≤ R'.upper :=
      ⟨hell.le.trans (hb z).1,(hb z).2.trans ((le_abs_self _).trans (R'.reference_bound z))⟩
    have hrb (z : Domain) : 0 ≤ R'.reference z-c z ∧ R'.reference z-c z ≤ R'.upper :=
      ⟨sub_nonneg.mpr (hb z).2,(sub_le_self _ (hcb z).1).trans ((le_abs_self _).trans (R'.reference_bound z))⟩
    refine ⟨ih h.1 hsup.1,
      profileCovariances_posSemidef L' c hc R'.upper_nonneg hcb k h,
      profileCovariances_posSemidef L' _ (R'.reference_measurable.sub hc) R'.upper_nonneg hrb k h,
      node_split L' c hc hell hb k h,?_⟩
    have he := profileCovariances_eq L L' hterminal hnode hobs (fun _=>ell) k h
    have hD : row L' k h∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (profileCovariances L' (fun _=>ell) k h)).range := by
      rw [←hrow k h,←he]
      exact hsup.2.2.2.2
    exact node_range_of_floor L' c hc hell hb hages k h hD

end SHE.HistorySupportedTransfer
