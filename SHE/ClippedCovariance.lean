module

public import SHE.CovarianceContinuity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SHE.ClippedCovariance
open MeasureTheory Set Filter SHE.WordRecursion SHE.CovarianceMatrix SHE.CovarianceContinuity
open SHE.GaussianContinuity
open scoped Topology MatrixOrder Matrix.Norms.Elementwise

def clip (a b t : ℝ) : ℝ := max a (min b t)

theorem clip_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clip a b t ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

theorem clip_monotone (a b : ℝ) : Monotone (clip a b) :=
  fun _ _ h => max_le_max_left a (min_le_min_left b h)

theorem continuous_clip (a b : ℝ) : Continuous (clip a b) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem lipschitz_clip (a b : ℝ) : LipschitzWith 1 (clip a b) :=
  (LipschitzWith.id.const_min b).const_max a

theorem clip_sub_clip_le (a b : ℝ) {u v : ℝ} (huv : u ≤ v) :
    clip a b v-clip a b u ≤ v-u := by
  have hh := (lipschitz_clip a b).dist_le_mul v u
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul,
    abs_of_nonneg (sub_nonneg.mpr (clip_monotone a b huv)),
    abs_of_nonneg (sub_nonneg.mpr huv)] using hh

theorem clip_eq {a b t : ℝ} (ht : t ∈ Icc a b) : clip a b t=t := by
  simp only [clip,min_eq_right ht.2,max_eq_right ht.1]

theorem clip_eq_near {a b q : ℝ} (hq : q ∈ Ioo a b) : clip a b =ᶠ[𝓝 q] id := by
  filter_upwards [isOpen_Ioo.mem_nhds hq] with t ht
  exact clip_eq (Ioo_subset_Icc_self ht)

/-- An actual bounded nonnegative reference profile and finite physical
observation window strictly before all its heat targets. -/
structure ObservationWindow (n : ℕ) where
  coefficient : ℝ × SHE.StoppedFourier.HeatCircle → ℝ
  measurable : Measurable coefficient
  observations : Fin n → Observation
  left : ℝ
  right : ℝ
  gap : ℝ
  upper : ℝ
  ordered : left ≤ right
  gap_pos : 0 < gap
  upper_nonneg : 0 ≤ upper
  target_gap : ∀ i,gap ≤ (observations i).target-right
  bounded : ∀ t ∈ Icc left right,∀ x,|coefficient (t,x)| ≤ upper
  nonneg : ∀ t ∈ Icc left right,∀ x,0 ≤ coefficient (t,x)

namespace ObservationWindow
variable {n : ℕ} (W : ObservationWindow n)

def path (t : ℝ) : PositiveCovariance n :=
  ⟨covariance W.coefficient W.observations (clip W.left W.right t) W.right,
    covariance_posSemidef W.coefficient W.measurable W.observations W.gap_pos W.upper_nonneg
      (clip_mem W.ordered t).2 W.target_gap
      (fun u hu => W.bounded u ⟨(clip_mem W.ordered t).1.trans hu.1,hu.2⟩)
      (fun u hu => W.nonneg u ⟨(clip_mem W.ordered t).1.trans hu.1,hu.2⟩)⟩

theorem continuous_path : Continuous W.path := by
  have hc : Continuous (fun t => covariance W.coefficient W.observations (clip W.left W.right t) W.right) :=
    (covariance_continuousOn_left W.coefficient W.measurable W.observations W.gap_pos
      W.upper_nonneg W.ordered W.target_gap W.bounded ⟨W.ordered,le_rfl⟩).comp_continuous
      (continuous_clip W.left W.right) (clip_mem W.ordered)
  exact hc.subtype_mk _

theorem path_antitone : Antitone (fun t => (W.path t).val) := by
  intro u v huv
  change (covariance W.coefficient W.observations (clip W.left W.right u) W.right-
    covariance W.coefficient W.observations (clip W.left W.right v) W.right).PosSemidef
  exact covariance_increment_posSemidef W.coefficient W.measurable W.observations W.gap_pos W.upper_nonneg
    (clip_monotone W.left W.right huv) (clip_mem W.ordered v).2 W.target_gap
    (fun t ht => W.bounded t ⟨(clip_mem W.ordered u).1.trans ht.1,ht.2⟩)
    (fun t ht => W.nonneg t ⟨(clip_mem W.ordered u).1.trans ht.1,ht.2⟩)

theorem path_eq {t : ℝ} (ht : t ∈ Icc W.left W.right) :
    (W.path t).val=covariance W.coefficient W.observations t W.right := by
  simp only [path,clip_eq ht]

theorem path_increment_trace_bound {u v : ℝ} (huv : u ≤ v) :
    ((W.path u).val-(W.path v).val).trace ≤
      (n:ℝ)*W.upper*(heatRowBound W.gap)^2*(v-u) := by
  have hh := covariance_increment_trace_bound W.coefficient W.measurable W.observations
    W.gap_pos W.upper_nonneg (clip_monotone W.left W.right huv) (clip_mem W.ordered v).2
    W.target_gap (fun t ht => W.bounded t ⟨(clip_mem W.ordered u).1.trans ht.1,ht.2⟩)
  exact hh.trans (mul_le_mul_of_nonneg_left (clip_sub_clip_le W.left W.right huv)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) W.upper_nonneg) (sq_nonneg _)))

theorem path_ae_hasDerivAt : ∀ᵐ q : ℝ,q ∈ Ioo W.left W.right →
    HasDerivAt (fun t => (W.path t).val) (-densityMatrix W.coefficient W.observations q) q := by
  have hh := covariance_ae_hasDerivAt_left W.coefficient W.measurable W.observations W.gap_pos
    W.upper_nonneg W.ordered W.target_gap W.bounded ⟨W.ordered,le_rfl⟩
  filter_upwards [hh] with q hq
  intro hqin
  have he : (fun t => (W.path t).val) =ᶠ[𝓝 q]
      fun t => covariance W.coefficient W.observations t W.right := by
    filter_upwards [clip_eq_near hqin] with t ht
    simp only [path,ht,id_eq]
  exact (hq (Ioo_subset_Icc_self hqin)).congr_of_eventuallyEq he

end ObservationWindow
end SHE.ClippedCovariance
