module

public import SHE.GaussianMatrixCurve

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.GaussianMatrixGramCurve
open Set MeasureTheory Filter Matrix GaussianContinuity GaussianCovariancePath ClippedCovariance
open scoped Matrix.Norms.Elementwise Topology

/-- The actual integrable finite Gram density of deterministic original
noise rows. Its associated backward curve is constructed below. -/
structure Density (n : ℕ) where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  value : ℝ → Mat n
  measurable : Measurable value
  positive : ∀ t, (value t).PosSemidef
  integrable : ∀ i j, IntervalIntegrable (fun t => value t i j) volume left right

def covariance {n : ℕ} (D : Density n) (q r : ℝ) : Mat n :=
  fun i j => ∫ t in q..r, D.value t i j

theorem entry_integrable {n : ℕ} (D : Density n) {q r : ℝ}
    (hq : D.left ≤ q) (hqr : q ≤ r) (hr : r ≤ D.right) (i j : Fin n) :
    IntervalIntegrable (fun t => D.value t i j) volume q r := by
  apply (D.integrable i j).mono_set
  simpa only [uIcc_of_le D.ordered, uIcc_of_le hqr] using Icc_subset_Icc hq hr

theorem covariance_positive {n : ℕ} (D : Density n) {q r : ℝ}
    (hq : D.left ≤ q) (hqr : q ≤ r) (hr : r ≤ D.right) :
    (covariance D q r).PosSemidef := by
  unfold covariance
  simp only [intervalIntegral.integral_of_le hqr]
  exact CovarianceMatrix.entry_integral_posSemidef (volume.restrict (Ioc q r)) D.value
    (fun i j => (entry_integrable D hq hqr hr i j).1) (ae_of_all _ D.positive)

theorem covariance_add {n : ℕ} (D : Density n) {q r s : ℝ}
    (hq : D.left ≤ q) (hqr : q ≤ r) (hrs : r ≤ s) (hs : s ≤ D.right) :
    covariance D q s = covariance D q r + covariance D r s := by
  ext i j
  exact (intervalIntegral.integral_add_adjacent_intervals
    (entry_integrable D hq hqr (hrs.trans hs) i j)
    (entry_integrable D (hq.trans hqr) hrs hs i j)).symm

theorem covariance_continuous {n : ℕ} (D : Density n) :
    ContinuousOn (fun q => covariance D q D.right) (Icc D.left D.right) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hh := (intervalIntegral.continuousOn_primitive_interval' (D.integrable i j)
    (by simp only [uIcc_of_le D.ordered]; exact ⟨D.ordered,le_rfl⟩)).neg
  have he : (fun q => -(∫ t in D.right..q, D.value t i j)) =
      fun q => covariance D q D.right i j := by
    funext q
    rw [intervalIntegral.integral_symm,neg_neg]
    rfl
  change ContinuousOn (fun q => -(∫ t in D.right..q, D.value t i j)) (uIcc D.left D.right) at hh
  rwa [he,uIcc_of_le D.ordered] at hh

def path {n : ℕ} (D : Density n) (t : ℝ) : PositiveCovariance n :=
  ⟨covariance D (clip D.left D.right t) D.right,
    covariance_positive D (clip_mem D.ordered t).1 (clip_mem D.ordered t).2 le_rfl⟩

theorem path_eq {n : ℕ} (D : Density n) {t : ℝ} (ht : t ∈ Icc D.left D.right) :
    (path D t).val = covariance D t D.right := by
  simp only [path,clip_eq ht]

theorem path_continuous {n : ℕ} (D : Density n) : Continuous (path D) := by
  have hc := (covariance_continuous D).comp_continuous
    (continuous_clip D.left D.right) (clip_mem D.ordered)
  exact hc.subtype_mk _

theorem path_order {n : ℕ} (D : Density n) (u v : ℝ) (huv : u ≤ v) :
    ((path D u).val - (path D v).val).PosSemidef := by
  change (covariance D (clip D.left D.right u) D.right -
    covariance D (clip D.left D.right v) D.right).PosSemidef
  rw [covariance_add D (clip_mem D.ordered u).1
    (clip_monotone D.left D.right huv) (clip_mem D.ordered v).2 le_rfl,
    add_sub_cancel_right]
  exact covariance_positive D (clip_mem D.ordered u).1
    (clip_monotone D.left D.right huv) (clip_mem D.ordered v).2

theorem path_derivative {n : ℕ} (D : Density n) :
    ∀ᵐ q : ℝ, q ∈ Ioo D.left D.right →
      HasDerivAt (fun t => (path D t).val) (-D.value q) q := by
  have he (i j : Fin n) : ∀ᵐ q : ℝ, q ∈ Icc D.left D.right →
      HasDerivAt (fun r => covariance D r D.right i j) (-D.value q i j) q := by
    filter_upwards [(D.integrable i j).ae_hasDerivAt_integral] with q hq
    intro hqa
    have hd := (hq (by simpa only [uIcc_of_le D.ordered] using hqa) D.right
      (by simp only [uIcc_of_le D.ordered]; exact ⟨D.ordered,le_rfl⟩)).neg
    have he : (fun r => -(∫ t in D.right..r, D.value t i j)) =
        fun r => covariance D r D.right i j := by
      funext r
      rw [intervalIntegral.integral_symm,neg_neg]
      rfl
    change HasDerivAt (fun r => -(∫ t in D.right..r, D.value t i j)) (-D.value q i j) q at hd
    rwa [he] at hd
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i))] with q hq
  intro hqa
  have hd : HasDerivAt (fun r => covariance D r D.right) (-D.value q) q := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    exact hq i j (Ioo_subset_Icc_self hqa)
  have heq : (fun t => (path D t).val) =ᶠ[𝓝 q] fun t => covariance D t D.right := by
    filter_upwards [clip_eq_near hqa] with t ht
    simp only [path,ht,id_eq]
  exact hd.congr_of_eventuallyEq heq

theorem path_trace_ac {n : ℕ} (D : Density n) :
    AbsolutelyContinuousOnInterval (fun t => (path D t).val.trace) D.left D.right := by
  have hdiag (i : Fin n) : AbsolutelyContinuousOnInterval
      (fun q => covariance D q D.right i i) D.left D.right := by
    have hh := ((D.integrable i i).absolutelyContinuousOnInterval_intervalIntegral
      (by simp only [uIcc_of_le D.ordered]; exact ⟨D.ordered,le_rfl⟩)).neg
    have he : (fun q => -(∫ t in D.right..q, D.value t i i)) =
        fun q => covariance D q D.right i i := by
      funext q
      rw [intervalIntegral.integral_symm,neg_neg]
      rfl
    change AbsolutelyContinuousOnInterval (fun q => -(∫ t in D.right..q, D.value t i i)) D.left D.right at hh
    rwa [he] at hh
  have hsum (S : Finset (Fin n)) : AbsolutelyContinuousOnInterval
      (fun q => ∑ i ∈ S, covariance D q D.right i i) D.left D.right := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact (LipschitzWith.const (0:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
    | @insert i S hi ih =>
      have hh := (hdiag i).add ih
      change AbsolutelyContinuousOnInterval (fun q => covariance D q D.right i i +
        ∑ j ∈ S, covariance D q D.right j j) D.left D.right at hh
      simpa only [Finset.sum_insert hi] using hh
  apply (hsum Finset.univ).congr
  intro t ht
  rw [uIcc_of_le D.ordered] at ht
  change (covariance D t D.right).trace = (path D t).val.trace
  rw [path_eq D ht]

def curve {n : ℕ} (D : Density n) : GaussianMatrixCurve.Curve n where
  left := D.left
  right := D.right
  ordered := D.ordered
  path := path D
  continuous_path := path_continuous D
  path_order := path_order D
  trace_ac := path_trace_ac D
  density := D.value
  density_measurable := D.measurable
  path_derivative := path_derivative D
  envelope := fun t => (D.value t).trace
  envelope_integrable := by
    convert! IntervalIntegrable.sum Finset.univ (fun i _ => D.integrable i i) using 1
    funext t
    simp [Matrix.trace]
  envelope_nonneg := fun t _ => (D.positive t).trace_nonneg
  density_bound := fun t _ i j => PositiveMatrixBounds.abs_entry_le_trace (D.positive t) i j
  terminal := by
    ext i j
    simp [path, covariance, clip, max_eq_right D.ordered]

end SHE.GaussianMatrixGramCurve
