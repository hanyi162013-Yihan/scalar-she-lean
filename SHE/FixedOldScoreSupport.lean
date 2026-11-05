module

public import SHE.RecursiveScoreSupport
public import SHE.IntervalGramRange

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FixedOldScoreSupport
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianRangeSmooth
  StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers OldIntervalCovariance
open scoped BigOperators Matrix.Norms.L2Operator
local instance fixedOldScoreSupport_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def profileCovariances (c : StoppedGaussianFeatures.Domain → ℝ) :
    RecursiveGaussianScores.Covariances (P := P) (n := n) := fun k p =>
  WordRecursion.covariance c ((carrier L k).observations.observations p.1)
    ((carrier L k).nodeTime p) ((carrier L k).terminal p.1)

theorem profileCovariances_measurable (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c) (k : ℕ) :
    Measurable (profileCovariances L c k) := by
  let Z : VariableObservations.Family (History P (k+1)) (n+k) :=
    CutoffWordLevel.reindexFamily (carrier L k).observations Prod.fst measurable_fst
  exact Z.covariance_measurable (hc.comp measurable_snd) (carrier L k).nodeTime_measurable
    ((carrier L k).terminal_measurable.comp measurable_fst) (fun p => ((carrier L k).nodeTime_mem p).2)

theorem profileCovariances_posSemidef (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (k : ℕ) (p : History P (k+1)) :
    (profileCovariances L c k p).PosSemidef :=
  CovarianceEndpoint.covariance_posSemidef_endpoint c hc _ hM ((carrier L k).nodeTime_mem p).2
    ((carrier L k).targets_after p.1)
    (fun t _ x => by rw [abs_of_nonneg (hb (t,x)).1]; exact (hb (t,x)).2)
    (fun t _ x => (hb (t,x)).1)

theorem node_split (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    (k : ℕ) (p : History P (k+1)) :
    ((carrier L k).nodeCovariance p).val =
      profileCovariances L c k p + profileCovariances L (fun p => R.reference p - c p) k p := by
  have hcb (p : StoppedGaussianFeatures.Domain) : |c p| ≤ R.upper := by
    rw [abs_of_nonneg (hell.le.trans (hb p).1)]
    exact (hb p).2.trans ((le_abs_self _).trans (R.reference_bound p))
  have hrb (p : StoppedGaussianFeatures.Domain) : |R.reference p - c p| ≤ R.upper := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hb p).2)]
    exact (sub_le_self _ (hell.le.trans (hb p).1)).trans ((le_abs_self _).trans (R.reference_bound p))
  have he := PhysicalIntervalCovariance.covariance_add ((carrier L k).observations.observations p.1)
    c (fun p => R.reference p - c p) hc (R.reference_measurable.sub hc) R.upper_nonneg R.upper_nonneg
    ((carrier L k).nodeTime_mem p).2 ((carrier L k).targets_after p.1) hcb hrb
  simpa only [profileCovariances, CutoffWordLevel.Level.nodeCovariance, add_sub_cancel] using he

theorem node_row_mem_old_range_ae (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (t : ℝ) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      row L k (p,t,x) ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariances L c k (p,t,x))).range := by
  by_cases ht : R.base < t ∧ t < (carrier L k).terminal p
  · let Z := (carrier L k).observations.observations p
    have hnode (x : HeatCircle) : (carrier L k).nodeTime (p,t,x) = t :=
      ClippedCovariance.clip_eq ⟨ht.1.le, ht.2.le⟩
    have hcb (z : StoppedGaussianFeatures.Domain) : ell ≤ c z ∧ c z ≤ R.upper :=
      ⟨(hb z).1, (hb z).2.trans ((le_abs_self _).trans (R.reference_bound z))⟩
    have hh := endpoint_row_mem_range_unrestricted (fun i => (Z i).stop) (fun i => (Z i).target)
      (fun i => (Z i).center) (RecursiveScoreSupport.carrier_ages L hages k p)
      (R.base_nonneg.trans ht.1.le) ht.2 (fun i => Or.inr ((carrier L k).stops_after p i)) c hc hell hcb
    rw [PhysicalIntervalCovariance.interval_eq_covariance Z c hc
      (fun z => by rw [abs_of_nonneg (hell.le.trans (hcb z).1)]; exact (hcb z).2)
      (RecursiveScoreSupport.carrier_ages L hages k p) ((carrier L k).stops_after p)
      (R.base_nonneg.trans ht.1.le) ht.2.le] at hh
    filter_upwards [hh] with x hx
    have he : StoppedGaussianFeatures.stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target)
        (fun i => (Z i).center) (t,x) = heatRow Z t x := by
      ext i
      change (if t < (Z i).stop then _ else 0) = _
      rw [ite_eq_left (show t < (Z i).stop from ht.2.trans_le ((carrier L k).stops_after p i))]
      rfl
    simpa only [he, row, Interior, ht.1, ht.2, and_self, ite_true, profileCovariances, hnode] using hx
  · exact ae_of_all _ (fun x => by
      simp only [row, Interior, ht, ite_false]
      exact Submodule.zero_mem _)

theorem supported_measurableSet (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p) (k : ℕ) :
    MeasurableSet {p : History P k | RecursiveGaussianScores.Supported L
      (profileCovariances L c) (profileCovariances L (fun p => R.reference p - c p)) k p} := by
  induction k with
  | zero => exact MeasurableSet.univ
  | succ k ih =>
    have hc0 (p : StoppedGaussianFeatures.Domain) : 0 ≤ c p ∧ c p ≤ R.upper :=
      ⟨hell.le.trans (hb p).1, (hb p).2.trans ((le_abs_self _).trans (R.reference_bound p))⟩
    have hr0 (p : StoppedGaussianFeatures.Domain) : 0 ≤ R.reference p - c p ∧ R.reference p - c p ≤ R.upper :=
      ⟨sub_nonneg.mpr (hb p).2, (sub_le_self _ (hc0 p).1).trans ((le_abs_self _).trans (R.reference_bound p))⟩
    have he : {p : History P (k+1) | RecursiveGaussianScores.Supported L
        (profileCovariances L c) (profileCovariances L (fun p => R.reference p - c p)) (k+1) p} =
        {p | RecursiveGaussianScores.Supported L (profileCovariances L c)
          (profileCovariances L (fun p => R.reference p - c p)) k p.1} ∩
        {p | row L k p ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariances L c k p)).range} := by
      ext p
      simp only [mem_inter_iff, Set.mem_ofPred_eq, RecursiveGaussianScores.Supported]
      have ho := profileCovariances_posSemidef L c hc R.upper_nonneg hc0 k p
      have hr : (profileCovariances L (fun z => R.reference z - c z) k p).PosSemidef :=
        profileCovariances_posSemidef L _ (R.reference_measurable.sub hc) R.upper_nonneg hr0 k p
      simp only [ho, hr, node_split L c hc hell hb k p, true_and]
    rw [he]
    exact (ih.preimage measurable_fst).inter
      (RecursiveScoreSupport.range_measurableSet _ _ (profileCovariances_measurable L c hc k) (row_measurable L k))

theorem supported_ae (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂historyMeasure R μ k, RecursiveGaussianScores.Supported L
      (profileCovariances L c) (profileCovariances L (fun p => R.reference p - c p)) k p := by
  induction k with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ k ih =>
    apply (Measure.ae_prod_iff_ae_ae (supported_measurableSet L c hc hell hb (k+1))).mpr
    filter_upwards [ih] with p hp
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · apply ae_of_all
      intro t
      filter_upwards [node_row_mem_old_range_ae L c hc hell hb hages k p t] with x hx
      refine ⟨hp, ?_, ?_, node_split L c hc hell hb k (p,t,x), hx⟩
      · exact profileCovariances_posSemidef L c hc R.upper_nonneg
          (fun z => ⟨hell.le.trans (hb z).1, (hb z).2.trans ((le_abs_self _).trans (R.reference_bound z))⟩) k (p,t,x)
      · exact profileCovariances_posSemidef L _ (R.reference_measurable.sub hc) R.upper_nonneg
          (fun z => ⟨sub_nonneg.mpr (hb z).2,
            (sub_le_self _ (hell.le.trans (hb z).1)).trans ((le_abs_self _).trans (R.reference_bound z))⟩) k (p,t,x)
    · exact (supported_measurableSet L c hc hell hb (k+1)).preimage (measurable_const.prodMk measurable_id)

end SHE.FixedOldScoreSupport
