module

public import SHE.PhysicalIntervalCovariance
public import SHE.RecursiveGaussianScores

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RecursiveScoreSupport
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianRangeSmooth
  StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
open scoped BigOperators Matrix.Norms.L2Operator
local instance recursiveScoreSupport_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

theorem carrier_stops_one (horizon : R.horizon ≤ 1)
    (hstop : ∀ p i, (L.observations.observations p i).stop ≤ 1) (k : ℕ) :
    ∀ p i, ((carrier L k).observations.observations p i).stop ≤ 1 := by
  induction k with
  | zero => exact hstop
  | succ k ih =>
    intro p i
    refine Fin.cases ?_ (fun j => ih p.1 j) i
    change (carrier L k).nodeTime p ≤ 1
    exact ((carrier L k).nodeTime_mem p).2.trans (((carrier L k).terminal_horizon p.1).trans horizon)

theorem carrier_ages (hages : ∀ p i, (L.observations.observations p i).stop ≤
    (L.observations.observations p i).target) (k : ℕ) :
    ∀ p i, ((carrier L k).observations.observations p i).stop ≤
      ((carrier L k).observations.observations p i).target := by
  induction k with
  | zero => exact hages
  | succ k ih =>
    intro p i
    refine Fin.cases ?_ (fun j => ih p.1 j) i
    change (carrier L k).nodeTime p ≤ (carrier L k).nodeTime p + 0
    exact le_add_of_nonneg_right le_rfl

theorem range_measurableSet {X : Type*} [MeasurableSpace X] {N : ℕ}
    (A : X → Matrix (Fin N) (Fin N) ℝ) (d : X → GaussianIncrement.State N)
    (hA : Measurable A) (hd : Measurable d) :
    MeasurableSet {x | d x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).range} := by
  have hg := MeasurableGeneralizedInverse.generalizedInverse_measurable.comp (hA.prodMk hd)
  have hi := MeasurableGeneralizedInverse.operator_apply_measurable.comp (hA.prodMk hg)
  have he : {x | d x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).range} =
      {x | Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)
        (MeasurableGeneralizedInverse.generalizedInverse (A x) (d x)) = d x} := by
    ext x
    exact ⟨fun hx => MeasurableGeneralizedInverse.generalizedInverse_on_range (A x) hx,
      fun hx => ⟨_, hx⟩⟩
  rw [he]
  exact measurableSet_eq_fun hi hd

/-- A genuine elliptic reference profile makes the physical insertion row
belong to the original covariance range almost everywhere, at every fixed
ancestral history and insertion time. Outside the interior the literal row
is zero, including all collision endpoints. -/
theorem node_row_mem_range_ae {ell : ℝ} (hell : 0 < ell)
    (href : ∀ p, ell ≤ R.reference p) (hh : R.horizon ≤ 1)
    (hstop : ∀ p i, (L.observations.observations p i).stop ≤ 1)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (t : ℝ) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      row L k (p, t, x) ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((carrier L k).nodeCovariance (p, t, x)).val).range := by
  by_cases ht : R.base < t ∧ t < (carrier L k).terminal p
  · have hnode (x : HeatCircle) : (carrier L k).nodeTime (p, t, x) = t :=
      ClippedCovariance.clip_eq ⟨ht.1.le, ht.2.le⟩
    have hrow := PhysicalIntervalCovariance.heatRow_mem_range_ae
      ((carrier L k).observations.observations p) R.reference R.reference_measurable hell
      (fun z => ⟨href z, (le_abs_self _).trans (R.reference_bound z)⟩)
      (carrier_ages L hages k p) ((carrier L k).stops_after p)
      (carrier_stops_one L hh hstop k p) (R.base_nonneg.trans ht.1.le) ht.2
    filter_upwards [hrow] with x hx
    simpa only [row, Interior, ht.1, ht.2, and_self, ite_true, CutoffWordLevel.Level.nodeCovariance, hnode] using hx
  · exact ae_of_all _ (fun x => by
      simp only [row, Interior, ht, ite_false]
      exact Submodule.zero_mem _)

def halfCovariances : RecursiveGaussianScores.Covariances (P := P) (n := n) :=
  fun k p => (1 / 2 : ℝ) • ((carrier L k).nodeCovariance p).val

theorem node_half_split (k : ℕ) (p : History P (k+1)) :
    ((carrier L k).nodeCovariance p).val = halfCovariances L k p + halfCovariances L k p := by
  simp only [halfCovariances, ← add_smul]
  norm_num

theorem supported_measurableSet (k : ℕ) :
    MeasurableSet {p : History P k |
      RecursiveGaussianScores.Supported L (halfCovariances L) (halfCovariances L) k p} := by
  induction k with
  | zero => exact MeasurableSet.univ
  | succ k ih =>
    have he : {p : History P (k+1) |
        RecursiveGaussianScores.Supported L (halfCovariances L) (halfCovariances L) (k+1) p} =
        {p | RecursiveGaussianScores.Supported L (halfCovariances L) (halfCovariances L) k p.1} ∩
        {p | row L k p ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) ((carrier L k).nodeCovariance p).val).range} := by
      ext p
      simp only [mem_inter_iff, Set.mem_ofPred_eq]
      change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _)
      have hp : (halfCovariances L k p).PosSemidef :=
        (((carrier L k).nodeCovariance p).property).smul (by norm_num : 0 ≤ (1 / 2 : ℝ))
      have hr : (Matrix.toEuclideanCLM (𝕜 := ℝ) (halfCovariances L k p)).range =
        (Matrix.toEuclideanCLM (𝕜 := ℝ) ((carrier L k).nodeCovariance p).val).range :=
          covariance_range_smul _ (by norm_num : (1 / 2 : ℝ) ≠ 0)
      constructor
      · intro h
        refine ⟨h.1, ?_⟩
        change row L k p ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) ((carrier L k).nodeCovariance p).val).range
        rw [← hr]
        exact h.2.2.2.2
      · intro h
        refine ⟨h.1, hp, hp, node_half_split L k p, ?_⟩
        rw [hr]
        exact h.2
    rw [he]
    exact (ih.preimage measurable_fst).inter
      (range_measurableSet _ _ (((carrier L k).nodeCovariance_measurable).subtype_val) (row_measurable L k))

theorem supported_ae (μ : Measure P) [IsFiniteMeasure μ] {ell : ℝ} (hell : 0 < ell)
    (href : ∀ p, ell ≤ R.reference p) (hh : R.horizon ≤ 1)
    (hstop : ∀ p i, (L.observations.observations p i).stop ≤ 1)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) :
    ∀ᵐ p ∂historyMeasure R μ k,
      RecursiveGaussianScores.Supported L (halfCovariances L) (halfCovariances L) k p := by
  induction k with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ k ih =>
    apply (Measure.ae_prod_iff_ae_ae (supported_measurableSet L (k+1))).mpr
    filter_upwards [ih] with p hp
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · apply ae_of_all
      intro t
      filter_upwards [node_row_mem_range_ae L hell href hh hstop hages k p t] with x hx
      refine ⟨hp, ?_, ?_, node_half_split L k (p,t,x), ?_⟩
      · exact (((carrier L k).nodeCovariance (p,t,x)).property).smul (by norm_num : 0 ≤ (1 / 2 : ℝ))
      · exact (((carrier L k).nodeCovariance (p,t,x)).property).smul (by norm_num : 0 ≤ (1 / 2 : ℝ))
      · simpa only [halfCovariances, covariance_range_smul _ (by norm_num : (1 / 2 : ℝ) ≠ 0)] using hx
    · exact (supported_measurableSet L (k+1)).preimage (measurable_const.prodMk measurable_id)

/-- The actual recursive uncut words have their literal nested Gaussian
score representation on almost every physical history. All range, PSD and
covariance-splitting obligations have been discharged. -/
theorem test_eq_scored_ae (μ : Measure P) [IsFiniteMeasure μ] {ell : ℝ} (hell : 0 < ell)
    (href : ∀ p, ell ≤ R.reference p) (hh : R.horizon ≤ 1)
    (hstop : ∀ p i, (L.observations.observations p i).stop ≤ 1)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) :
    ∀ᵐ p ∂historyMeasure R μ k,
      UncutSmoothWords.test L k p =
        RecursiveGaussianScores.scored L (halfCovariances L) (halfCovariances L) k p :=
  (supported_ae L μ hell href hh hstop hages k).mono
    (fun _ hp => RecursiveGaussianScores.test_eq_scored L _ _ _ _ hp)

end SHE.RecursiveScoreSupport
