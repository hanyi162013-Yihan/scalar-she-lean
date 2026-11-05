module

public import SHE.JointRecursiveHessian
public import SHE.JointInsertionBounds
public import SHE.PhysicalRemainderMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.JointRecursiveRemainderLimit
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds RecursiveHeatTargets CutoffWordAnalytic Filter Topology
open PhysicalIto PhysicalRemainderBound PhysicalRemainderMass
open scoped NNReal
local instance jointRecursiveRemainderLimit_period : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance jointRecursiveRemainderLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance jointRecursiveRemainderLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

theorem continuous_insertion (k : ℕ) (p : History P k) (ω : Ω) {t : ℝ}
    (ht : t∈Ioo R.base ((level L δ hδ 0 k).terminal p)) (x : HeatCircle) :
    Continuous (fun ε : ℝ≥0 => JointWordAnalytic.insertion (level L δ hδ ε k) Λ U V XU XV p ω t x) := by
  let Z := fun ε : ℝ≥0 => (level L δ hδ ε k).observations.observations p
  let centers := fun i => (Z 0 i).center
  have htarget (ε : ℝ≥0) (i : Fin (n+k)) : (level L δ hδ 0 k).terminal p≤(Z ε i).target := by
    rw [← terminal_eq L δ hδ ε 0 k p]
    exact (level L δ hδ ε k).targets_after p i
  have hH := JointRecursiveHessian.continuous_field L δ hδ Λ U V XU XV k p ω ht.2
  have hrow : Continuous (fun ε : ℝ≥0 => heatRow (Z ε) t x) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+k) => ℝ)).comp
    apply continuous_pi
    intro i
    exact CovarianceTargetContinuity.continuous_heatRow Z centers (target_continuous L δ hδ k p)
      (fun ε i => center_eq L δ hδ ε 0 k p i) ht.2 htarget x i
  have hc := (continuous_const (y := (1/2:ℝ)*(R.totalVariance (XV (ω,(t,x)))-R.reference (t,x)))).mul
    ((hH.clm_apply hrow).clm_apply hrow)
  convert hc using 1
  funext ε
  exact JointPhysicalInsertion.insertion_appendState R.totalVariance R.reference (Z ε) t x _ _ _

def spatial (ε : ℝ≥0) (k : ℕ) (p : History P k) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ x : HeatCircle,JointWordAnalytic.insertion (level L δ hδ ε k) Λ U V XU XV p ω t x ∂haarAddCircle

theorem spatial_measurable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV) (ε : ℝ≥0) (k : ℕ) :
    Measurable (fun q : (History P k × Ω) × ℝ => spatial L δ hδ Λ U V XU XV ε k q.1.1 q.1.2 q.2) :=
  (JointWordAnalytic.insertion_measurable (level L δ hδ ε k) Λ hU hV hXU hXV).stronglyMeasurable.integral_prod_right'.measurable

theorem continuous_spatial (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
    (k : ℕ) (p : History P k) (ω : Ω) {t : ℝ}
    (ht : t ∈ Ioo R.base ((level L δ hδ 0 k).terminal p)) :
    Continuous (fun ε : ℝ≥0 => spatial L δ hδ Λ U V XU XV ε k p ω t) := by
  obtain ⟨A,hA⟩ := R.totalVariance_smooth.norm_bound
  have hAn : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ k).norm_bound
  obtain ⟨D,_,hD⟩ := (test_uniform L δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (test_uniform L δ hδ k).fderiv.fderiv.norm_bound
  let s := (level L δ hδ 0 k).terminal p
  let Q := Real.sqrt ((n+k:ℕ):ℝ)*CovarianceMatrix.heatRowBound (s-t)
  have hQ : 0 ≤ Q := mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos (sub_pos.mpr ht.2)).le
  let K := (1/2:ℝ)*(A+R.upper)*B*Q^2
  have hb (ε : ℝ≥0) (x : HeatCircle) :
      ‖JointWordAnalytic.insertion (level L δ hδ ε k) Λ U V XU XV p ω t x‖ ≤ K := by
    have hte : t ∈ Ioo ((level L δ hδ ε k).window p).left ((level L δ hδ ε k).window p).right := by
      change t ∈ Ioo R.base ((level L δ hδ ε k).terminal p)
      rw [terminal_eq L δ hδ ε 0 k p]
      exact ht
    have hHb : ∀ z,‖GaussianTaylor.hessian (GaussianItoTest.backward
        ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) z‖ ≤ B :=
      fun z => BackwardRegularity.gaussian_state_hessian_bound _
        (((level L δ hδ ε k).test_uniform.smooth p).of_le (by simp)) (hC (ε,p)) (hD (ε,p)) (hB (ε,p)) z
    have hh := JointInsertionBounds.pointwise_bound ((level L δ hδ ε k).window p) hAn
      (fun z => by simpa only [Real.norm_eq_abs] using hA z) hBn (fun q => XV (ω,q))
      hte (GaussianItoTest.backward ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) (JointWordAnalytic.state (level L δ hδ ε k) Λ U V XU XV p ω t) (hHb _) x
    have hr : ‖heatRow ((level L δ hδ ε k).observations.observations p) t x‖ ≤ Q :=
      UniformInsertions.heatRow_norm_bound ((level L δ hδ ε k).observations.observations p)
        (t := t) (sub_pos.mpr ht.2) (fun i => by
        have htar := (level L δ hδ ε k).targets_after p i
        rw [terminal_eq L δ hδ ε 0 k p] at htar
        linarith) x
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 2)
      (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hAn R.upper_nonneg)) hBn))
  apply continuous_of_dominated (bound := fun _ : HeatCircle => K)
  · intro ε
    exact ((JointWordAnalytic.insertion_measurable (level L δ hδ ε k) Λ hU hV hXU hXV).comp
      ((measurable_const (a := ((p,ω),t))).prodMk measurable_id)).aestronglyMeasurable
  · exact fun ε => Eventually.of_forall (hb ε)
  · exact integrable_const _
  · exact Eventually.of_forall (continuous_insertion L δ hδ Λ U V XU XV k p ω ht)

end SHE.JointRecursiveRemainderLimit
