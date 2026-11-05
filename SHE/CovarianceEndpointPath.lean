module

public import SHE.CovarianceEndpoint
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.CovarianceEndpoint
open MeasureTheory Set Finset Matrix WordRecursion CovarianceMatrix ClippedCovariance
open GaussianContinuity StoppedFourier
open scoped Topology MatrixOrder Matrix.Norms.Elementwise

theorem covariance_add_interval_endpoint {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {M q r s : ℝ} (hM : 0 ≤ M) (hqr : q ≤ r) (hrs : r ≤ s)
    (hgap : ∀ i,s ≤ (Z i).target) (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M) :
    covariance c Z q s=covariance c Z q r+covariance c Z r s := by
  apply Matrix.ext
  intro i j
  have hi := covariance_entry_intervalIntegrable_endpoint c hc Z hM (hqr.trans hrs) hgap hbound i j
  have h₁ : IntervalIntegrable (fun t => covarianceDensity c Z t i j) volume q r :=
    hi.mono_set (by simpa only [uIcc_of_le hqr,uIcc_of_le (hqr.trans hrs)] using Icc_subset_Icc le_rfl hrs)
  have h₂ : IntervalIntegrable (fun t => covarianceDensity c Z t i j) volume r s :=
    hi.mono_set (by simpa only [uIcc_of_le hrs,uIcc_of_le (hqr.trans hrs)] using Icc_subset_Icc hqr le_rfl)
  exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm

theorem covariance_increment_posSemidef_endpoint {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {M q r s : ℝ} (hM : 0 ≤ M) (hqr : q ≤ r) (hrs : r ≤ s)
    (hgap : ∀ i,s ≤ (Z i).target) (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M)
    (hnonneg : ∀ t ∈ Icc q s,∀ x,0 ≤ c (t,x)) :
    (covariance c Z q s-covariance c Z r s).PosSemidef := by
  rw [covariance_add_interval_endpoint c hc Z hM hqr hrs hgap hbound,add_sub_cancel_right]
  exact covariance_posSemidef_endpoint c hc Z hM hqr (fun i => hrs.trans (hgap i))
    (fun t ht => hbound t ⟨ht.1,ht.2.trans hrs⟩)
    (fun t ht => hnonneg t ⟨ht.1,ht.2.trans hrs⟩)

theorem covariance_continuousOn_endpoint {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {M a b : ℝ} (hM : 0 ≤ M) (hab : a ≤ b)
    (hgap : ∀ i,b ≤ (Z i).target) (hbound : ∀ t ∈ Icc a b,∀ x,|c (t,x)| ≤ M) :
    ContinuousOn (fun q => covariance c Z q b) (Icc a b) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hi := covariance_entry_intervalIntegrable_endpoint c hc Z hM hab hgap hbound i j
  have hh := (intervalIntegral.continuousOn_primitive_interval' hi
    (by simp only [uIcc_of_le hab]; exact ⟨hab,le_rfl⟩)).neg
  have he : (fun q => -(∫ t in b..q,covarianceDensity c Z t i j)) =
      fun q => covariance c Z q b i j := by
    funext q
    rw [intervalIntegral.integral_symm,neg_neg]
    rfl
  change ContinuousOn (fun q => -(∫ t in b..q,covarianceDensity c Z t i j)) (uIcc a b) at hh
  rwa [he,uIcc_of_le hab] at hh

theorem covariance_ae_hasDerivAt_endpoint {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {M a b : ℝ} (hM : 0 ≤ M) (hab : a ≤ b)
    (hgap : ∀ i,b ≤ (Z i).target) (hbound : ∀ t ∈ Icc a b,∀ x,|c (t,x)| ≤ M) :
    ∀ᵐ q : ℝ,q ∈ Icc a b → HasDerivAt (fun r => covariance c Z r b) (-densityMatrix c Z q) q := by
  have hh : ∀ i j : Fin n,∀ᵐ q : ℝ,q ∈ Icc a b →
      HasDerivAt (fun r => covariance c Z r b i j) (-covarianceDensity c Z q i j) q := by
    intro i j
    have hi := covariance_entry_intervalIntegrable_endpoint c hc Z hM hab hgap hbound i j
    filter_upwards [hi.ae_hasDerivAt_integral] with q hq
    intro hqa
    have hd := (hq (by simpa only [uIcc_of_le hab] using hqa) b
      (by simp only [uIcc_of_le hab]; exact ⟨hab,le_rfl⟩)).neg
    have he : (fun r => -(∫ t in b..r,covarianceDensity c Z t i j)) =
        fun r => covariance c Z r b i j := by
      funext r
      rw [intervalIntegral.integral_symm,neg_neg]
      rfl
    change HasDerivAt (fun r => -(∫ t in b..r,covarianceDensity c Z t i j)) (-covarianceDensity c Z q i j) q at hd
    rwa [he] at hd
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hh i))] with q hq
  intro hqa
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hq i j hqa

/-- The actual covariance trace is absolutely continuous up to a zero
terminal heat age, because its true heat-square singularity is integrable. -/
theorem covariance_trace_absolutelyContinuous_endpoint {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {M a b : ℝ} (hM : 0 ≤ M) (hab : a ≤ b)
    (hgap : ∀ i,b ≤ (Z i).target) (hbound : ∀ t ∈ Icc a b,∀ x,|c (t,x)| ≤ M) :
    AbsolutelyContinuousOnInterval (fun q => (covariance c Z q b).trace) a b := by
  have hdiag (i : Fin n) : AbsolutelyContinuousOnInterval (fun q => covariance c Z q b i i) a b := by
    have hi := covariance_entry_intervalIntegrable_endpoint c hc Z hM hab hgap hbound i i
    have hh := (hi.absolutelyContinuousOnInterval_intervalIntegral
      (by simp only [uIcc_of_le hab]; exact ⟨hab,le_rfl⟩)).neg
    have he : (fun q => -(∫ t in b..q,covarianceDensity c Z t i i)) =
        fun q => covariance c Z q b i i := by
      funext q
      rw [intervalIntegral.integral_symm,neg_neg]
      rfl
    change AbsolutelyContinuousOnInterval (fun q => -(∫ t in b..q,covarianceDensity c Z t i i)) a b at hh
    rwa [he] at hh
  have hsum (S : Finset (Fin n)) :
      AbsolutelyContinuousOnInterval (fun q => ∑ i ∈ S,covariance c Z q b i i) a b := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact (LipschitzWith.const (0:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
    | @insert i S hi ih =>
      have hh := (hdiag i).add ih
      change AbsolutelyContinuousOnInterval (fun q => covariance c Z q b i i+
        ∑ j ∈ S,covariance c Z q b j j) a b at hh
      simpa only [Finset.sum_insert hi] using hh
  exact hsum Finset.univ

structure EndpointWindow (n : ℕ) where
  coefficient : ℝ × HeatCircle → ℝ
  measurable : Measurable coefficient
  observations : Fin n → Observation
  left : ℝ
  right : ℝ
  upper : ℝ
  ordered : left ≤ right
  upper_nonneg : 0 ≤ upper
  target_after : ∀ i,right ≤ (observations i).target
  bounded : ∀ t ∈ Icc left right,∀ x,|coefficient (t,x)| ≤ upper
  nonneg : ∀ t ∈ Icc left right,∀ x,0 ≤ coefficient (t,x)

namespace EndpointWindow
variable {n : ℕ} (W : EndpointWindow n)

def path (t : ℝ) : PositiveCovariance n :=
  ⟨covariance W.coefficient W.observations (clip W.left W.right t) W.right,
    covariance_posSemidef_endpoint W.coefficient W.measurable W.observations W.upper_nonneg
      (clip_mem W.ordered t).2 W.target_after
      (fun u hu => W.bounded u ⟨(clip_mem W.ordered t).1.trans hu.1,hu.2⟩)
      (fun u hu => W.nonneg u ⟨(clip_mem W.ordered t).1.trans hu.1,hu.2⟩)⟩

theorem continuous_path : Continuous W.path := by
  have hc : Continuous (fun t => covariance W.coefficient W.observations (clip W.left W.right t) W.right) :=
    (covariance_continuousOn_endpoint W.coefficient W.measurable W.observations W.upper_nonneg
      W.ordered W.target_after W.bounded).comp_continuous
      (continuous_clip W.left W.right) (clip_mem W.ordered)
  exact hc.subtype_mk _

theorem path_antitone : Antitone (fun t => (W.path t).val) := by
  intro u v huv
  change (covariance W.coefficient W.observations (clip W.left W.right u) W.right-
    covariance W.coefficient W.observations (clip W.left W.right v) W.right).PosSemidef
  exact covariance_increment_posSemidef_endpoint W.coefficient W.measurable W.observations W.upper_nonneg
    (clip_monotone W.left W.right huv) (clip_mem W.ordered v).2 W.target_after
    (fun t ht => W.bounded t ⟨(clip_mem W.ordered u).1.trans ht.1,ht.2⟩)
    (fun t ht => W.nonneg t ⟨(clip_mem W.ordered u).1.trans ht.1,ht.2⟩)

theorem path_eq {t : ℝ} (ht : t ∈ Icc W.left W.right) :
    (W.path t).val=covariance W.coefficient W.observations t W.right := by
  simp only [path,clip_eq ht]

theorem path_ae_hasDerivAt : ∀ᵐ q : ℝ,q ∈ Ioo W.left W.right →
    HasDerivAt (fun t => (W.path t).val) (-densityMatrix W.coefficient W.observations q) q := by
  have hh := covariance_ae_hasDerivAt_endpoint W.coefficient W.measurable W.observations W.upper_nonneg
    W.ordered W.target_after W.bounded
  filter_upwards [hh] with q hq
  intro hqin
  have he : (fun t => (W.path t).val) =ᶠ[𝓝 q]
      fun t => covariance W.coefficient W.observations t W.right := by
    filter_upwards [clip_eq_near hqin] with t ht
    simp only [path,ht,id_eq]
  exact (hq (Ioo_subset_Icc_self hqin)).congr_of_eventuallyEq he

theorem path_trace_absolutelyContinuous :
    AbsolutelyContinuousOnInterval (fun t => (W.path t).val.trace) W.left W.right := by
  apply (covariance_trace_absolutelyContinuous_endpoint W.coefficient W.measurable W.observations
    W.upper_nonneg W.ordered W.target_after W.bounded).congr
  intro t ht
  rw [uIcc_of_le W.ordered] at ht
  change (covariance W.coefficient W.observations t W.right).trace=(W.path t).val.trace
  rw [W.path_eq ht]

end EndpointWindow
end SHE.CovarianceEndpoint
