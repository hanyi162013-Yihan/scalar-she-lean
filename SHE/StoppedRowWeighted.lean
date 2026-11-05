module

public import SHE.HeatRowWeighted
public import SHE.StoppedGaussianFeatures

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Genuine weighted integrability of the complete individually stopped
physical row. Each observation retains its own stopping window and target;
no common terminal window or inverse covariance bound is assumed. -/
namespace SHE.StoppedRowWeighted
open Set MeasureTheory AddCircle Finset StoppedFourier ProfileVariance
  StoppedGaussianFeatures WordRecursion
open scoped Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)

theorem historyMeasure_restrict_stop (s : ℝ) :
    (historyMeasure 0).restrict ((Ioc 0 s) ×ˢ (univ : Set HeatCircle)) =
      HeatRowWeighted.sourceMeasure s := by
  rw [historyMeasure, HeatRowWeighted.sourceMeasure,
    Measure.restrict_prod_eq_prod_univ, Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_restrict_of_subset (by
    intro p hp
    exact ⟨hp.1.1.le, mem_univ _⟩)

theorem historyMeasure_mono {q r : ℝ} (hqr : q ≤ r) : historyMeasure r ≤ historyMeasure q := by
  exact Measure.prod_mono (Measure.restrict_mono (Set.Ici_subset_Ici.mpr hqr) le_rfl) le_rfl

/-- Each stopped scalar row is integrable with its own true endpoint
singularity, including the zero target-stop gap. -/
theorem weighted_stopped_entry_integrable
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1)
    (hages : ∀ i, σ i ≤ target i) {a : ℝ} (ha : -1 < a) (i : Fin n) :
    Integrable (fun p : Domain => p.1 ^ a * stoppedRow σ target center p i ^ 2)
      (historyMeasure 0) := by
  let Z : Fin 1 → Observation := fun _ => ⟨σ i, target i, center i⟩
  have hi := HeatRowWeighted.weighted_heatRow_integrable Z (hσ i) (hσ1 i) ha
    (fun _ => hages i)
  have heq : (fun p : Domain => p.1 ^ a * ‖heatRow Z p.1 p.2‖ ^ 2) =
      fun p => p.1 ^ a * (heatPhysical (target i - p.1) (center i) p.2).re ^ 2 := by
    funext p
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_one, heatRow, PiLp.toLp_apply, Z]
  rw [heq] at hi
  have his : IntegrableOn (fun p : Domain => p.1 ^ a *
      (heatPhysical (target i - p.1) (center i) p.2).re ^ 2)
      ((Ioc 0 (σ i)) ×ˢ (univ : Set HeatCircle)) (historyMeasure 0) := by
    change Integrable _ ((historyMeasure 0).restrict _)
    rw [historyMeasure_restrict_stop]
    exact hi
  have hindicator := (integrable_indicator_iff (measurableSet_Ioc.prod MeasurableSet.univ)).mpr his
  have ht0 : ∀ᵐ p : Domain ∂historyMeasure 0, 0 < p.1 := by
    have htime : ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)), 0 < t := by
      filter_upwards [ae_restrict_mem measurableSet_Ici,
        ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht hn
      exact lt_of_le_of_ne ht hn.symm
    exact Measure.quasiMeasurePreserving_fst.ae htime
  have htσ : ∀ᵐ p : Domain ∂historyMeasure 0, p.1 ≠ σ i :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae (volume.ae_ne (σ i)))
  apply hindicator.congr
  filter_upwards [ht0, htσ] with p hp hn
  by_cases hs : p.1 < σ i
  · simp only [Set.indicator, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
      ite_eq_left (show 0 < p.1 ∧ p.1 ≤ σ i from ⟨hp, hs.le⟩),
      stoppedRow, ite_eq_left hs]
  · have hle : ¬p.1 ≤ σ i := by exact fun h => hs (lt_of_le_of_ne h hn)
    simp only [Set.indicator, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
      hle, and_false, ite_false, stoppedRow, ite_eq_right hs, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- The complete original stopped frame has a genuine integrable power
weight for every exponent greater than −1. -/
theorem weighted_stopped_row_integrable
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1)
    (hages : ∀ i, σ i ≤ target i) {a : ℝ} (ha : -1 < a) :
    Integrable (fun p : Domain => p.1 ^ a * ‖stoppedRow σ target center p‖ ^ 2)
      (historyMeasure 0) := by
  have hi := integrable_finsetSum univ (fun i _ =>
    weighted_stopped_entry_integrable σ target center hσ hσ1 hages ha i)
  convert! hi using 1
  funext p
  rw [EuclideanSpace.real_norm_sq_eq, mul_sum]

theorem weighted_stopped_row_integrable_cutoff
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1)
    (hages : ∀ i, σ i ≤ target i) {a : ℝ} (ha : -1 < a) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun p : Domain => p.1 ^ a * ‖stoppedRow σ target center p‖ ^ 2)
      (historyMeasure q) :=
  (weighted_stopped_row_integrable σ target center hσ hσ1 hages ha).mono_measure
    (historyMeasure_mono hq)

end SHE.StoppedRowWeighted
