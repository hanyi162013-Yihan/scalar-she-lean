module

public import SHE.ApproximationClock
public import SHE.HeatColumnSemigroup
public import SHE.RealHaarIntegrand

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarKernelApproximation
open MeasureTheory Set Filter AddCircle CircleHeat FiniteHaar ApproximationClock
open scoped Topology
local instance haarKernelApproximation_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
abbrev Columns := RealHaarIntegrand.Columns

theorem kernel_zero {ell M t : ℝ} (hell : 0 < ell) (ht : t ≤ 0) (f : EllipticField ell M) :
    RealHaarIntegrand.kernel ell M hell (t,f)=0 := by
  apply lp.ext
  funext q
  change DyadicApproximation.realPart (HaarHeatIntegrand.kernel ell M hell (t,f) q)=0
  rw [HaarHeatIntegrand.kernel_apply,ite_eq_right (not_lt.mpr ht)]
  change (Complex.reCLM.compLpL 2 haarAddCircle) (0:CircleL2)=0
  exact map_zero _

theorem continuousAt_real_kernel {ell M t : ℝ} (hell : 0 < ell) (ht : 0 < t) (f : EllipticField ell M) :
    ContinuousAt (fun r => RealHaarIntegrand.kernel ell M hell (r,f)) t := by
  have hc := HeatColumnSemigroup.continuousAt_kernel hell ht f
  have hn (r : ℝ) :
      ‖RealHaarIntegrand.kernel ell M hell (r,f)-RealHaarIntegrand.kernel ell M hell (t,f)‖=
        ‖HaarHeatIntegrand.kernel ell M hell (r,f)-HaarHeatIntegrand.kernel ell M hell (t,f)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (RealHaarIntegrand.kernel_difference_norm_sq ell M hell _ _)
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero] at hc ⊢
  simpa only [hn] using hc

/-- On each outer time cell the integral stops at its left endpoint,
while heat is evaluated at the right endpoint. This keeps both adaptedness
and domination by the true heat column energy. -/
def approximant (ell M : ℝ) (hell : 0 < ell) (n : ℕ) (t s : ℝ) (f : EllipticField ell M) : Columns :=
  if s ≤ left n t then RealHaarIntegrand.kernel ell M hell (right n t-s,f) else 0

theorem approximant_tendsto {ell M t s : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (f : EllipticField ell M) :
    Tendsto (fun n => approximant ell M hell n t s f) atTop
      (𝓝 (RealHaarIntegrand.kernel ell M hell (t-s,f))) := by
  by_cases hst : s < t
  · have hk := (continuousAt_real_kernel hell (sub_pos.mpr hst) f).tendsto.comp
      ((right_tendsto ht.le).sub_const s)
    have he := (left_tendsto ht.le).eventually (lt_mem_nhds hst)
    apply hk.congr'
    filter_upwards [he] with n hn
    simp only [approximant,ite_eq_left hn.le,Function.comp_apply]
  · have hst' : t ≤ s := le_of_not_gt hst
    have hz (n : ℕ) : approximant ell M hell n t s f=0 := by
      have hn : ¬ s ≤ left n t := not_le.mpr ((left_bounds n ht).2.1.trans_le hst')
      simp only [approximant,ite_eq_right hn]
    simp only [hz,kernel_zero hell (sub_nonpos.mpr hst') f]
    exact tendsto_const_nhds

theorem approximant_norm_sq_le {ell M t s : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (f : EllipticField ell M) (n : ℕ) :
    ‖approximant ell M hell n t s f‖^2 ≤ ‖RealHaarIntegrand.kernel ell M hell (t-s,f)‖^2 := by
  by_cases hs : s ≤ left n t
  · have hst : s < t := hs.trans_lt (left_bounds n ht).2.1
    have hδ : 0 ≤ right n t-t := sub_nonneg.mpr (right_bounds n ht.le).1
    have hk := HeatColumnSemigroup.kernel_forward hell (sub_pos.mpr hst) hδ f
    have he : (t-s)+(right n t-t)=right n t-s := by ring
    rw [he] at hk
    rw [approximant,ite_eq_left hs,RealHaarIntegrand.kernel_norm_sq,RealHaarIntegrand.kernel_norm_sq,hk]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (HeatColumnSemigroup.operator_contraction _ _) 2
  · simp only [approximant,ite_eq_right hs,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),sq_nonneg]

theorem approximant_difference_bound {ell M t s : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (f : EllipticField ell M) (n : ℕ) :
    ‖approximant ell M hell n t s f-RealHaarIntegrand.kernel ell M hell (t-s,f)‖^2 ≤
      4*‖RealHaarIntegrand.kernel ell M hell (t-s,f)‖^2 := by
  have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (approximant_norm_sq_le (s := s) hell ht f n)
  have hb : ‖approximant ell M hell n t s f-RealHaarIntegrand.kernel ell M hell (t-s,f)‖ ≤
      2*‖RealHaarIntegrand.kernel ell M hell (t-s,f)‖ := (norm_sub_le _ _).trans (by linarith)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using hs

section Measurable
local instance haarKernelApproximation_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance haarKernelApproximation_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance haarKernelApproximation_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarKernelApproximation_columnsBorel : BorelSpace Columns := ⟨rfl⟩

theorem approximant_measurable (ell M : ℝ) (hell : 0 < ell) (n : ℕ) :
    Measurable (fun p : (ℝ × ℝ) × EllipticField ell M => approximant ell M hell n p.1.1 p.1.2 p.2) := by
  classical
  have hm := (RealHaarIntegrand.kernel_measurable ell M hell).comp
    ((((right_measurable n).comp measurable_fst.fst).sub measurable_fst.snd).prodMk measurable_snd)
  exact hm.ite (measurableSet_le measurable_fst.snd ((left_measurable n).comp measurable_fst.fst)) measurable_const

end Measurable

end SHE.HaarKernelApproximation
