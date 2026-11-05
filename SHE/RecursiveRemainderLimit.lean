module

public import SHE.RecursiveHeatTestContinuity
public import SHE.ObservationTargetContinuity
public import SHE.PhysicalRemainderMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.RecursiveRemainderLimit
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds RecursiveHeatTargets CutoffWordAnalytic Filter Topology
open PhysicalIto PhysicalRemainderBound PhysicalRemainderMass
open scoped NNReal
local instance recursiveRemainderLimit_period : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance recursiveRemainderLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance recursiveRemainderLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)
variable (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)

theorem continuous_backward_hessian (k : ℕ) (p : History P k) (t : ℝ) :
    Continuous (fun q : ℝ≥0 × WordRecursion.State (n+k) => GaussianTaylor.hessian
      (GaussianItoTest.backward ((level L δ hδ q.1 k).window p) ((level L δ hδ q.1 k).test p) t) q.2) := by
  have hF := RecursiveHeatTestContinuity.continuous_test L δ hδ k p
  have hFs := CutoffWordLevel.uniform_reindex (test_uniform L δ hδ k) (fun ε : ℝ≥0 => (ε,p))
  have hA := nodeCovariance_continuous L δ hδ k (p,(t,0))
  exact GaussianParameterContinuity.continuous_average_hessian
    (fun ε => (level L δ hδ ε k).test p) hF hFs
    (fun ε => (level L δ hδ ε k).nodeCovariance (p,(t,0))) hA

theorem continuous_insertedWord (k : ℕ) (p : History P k) (ω : Ω) {t : ℝ}
    (ht : t ∈ Ioo R.base ((level L δ hδ 0 k).terminal p)) (x : HeatCircle) :
    Continuous (fun ε : ℝ≥0 => insertedWord ((level L δ hδ ε k).window p)
      R.totalVariance (fun s => U (ω,s)) (fun q => X (ω,q)) ((level L δ hδ ε k).test p) t x) := by
  let Z := fun ε : ℝ≥0 => (level L δ hδ ε k).observations.observations p
  let centers := fun i => (Z 0 i).center
  have htarget (ε : ℝ≥0) (i : Fin (n+k)) : (level L δ hδ 0 k).terminal p ≤ (Z ε i).target := by
    rw [← terminal_eq L δ hδ ε 0 k p]
    exact (level L δ hδ ε k).targets_after p i
  have hold := ObservationTargetContinuity.continuous_observe Z centers
    (target_continuous L δ hδ k p) (fun ε i => center_eq L δ hδ ε 0 k p i)
    t (fun ε i => ht.2.trans_le (htarget ε i)) (fun s => U (ω,s)) (fun q => X (ω,q))
  have hH := (continuous_backward_hessian L δ hδ k p t).comp (continuous_id.prodMk hold)
  have hrow : Continuous (fun ε : ℝ≥0 => heatRow (Z ε) t x) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+k) => ℝ)).comp
    apply continuous_pi
    intro i
    exact CovarianceTargetContinuity.continuous_heatRow Z centers (target_continuous L δ hδ k p)
      (fun ε i => center_eq L δ hδ ε 0 k p i) ht.2 htarget x i
  have hd := (hH.clm_apply hrow).clm_apply hrow
  have hc := (continuous_const (y := (1/2:ℝ)*(R.totalVariance (X (ω,(t,x)))-R.reference (t,x)))).mul hd
  convert hc using 1
  funext ε
  exact insertion_observe R.totalVariance R.reference (fun s => U (ω,s))
    (fun q => X (ω,q)) (Z ε) t x _

def spatial (ε : ℝ≥0) (k : ℕ) (p : History P k) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ x : HeatCircle,insertedWord ((level L δ hδ ε k).window p) R.totalVariance
    (fun s => U (ω,s)) (fun q => X (ω,q)) ((level L δ hδ ε k).test p) t x ∂haarAddCircle

theorem spatial_measurable (hU : Measurable U) (hX : Measurable X) (ε : ℝ≥0) (k : ℕ) :
    Measurable (fun q : (History P k × Ω) × ℝ => spatial L δ hδ U X ε k q.1.1 q.1.2 q.2) :=
  (physical_insertion_measurable (level L δ hδ ε k) hU hX).stronglyMeasurable.integral_prod_right'.measurable

theorem continuous_spatial (hU : Measurable U) (hX : Measurable X)
    (k : ℕ) (p : History P k) (ω : Ω) {t : ℝ}
    (ht : t ∈ Ioo R.base ((level L δ hδ 0 k).terminal p)) :
    Continuous (fun ε : ℝ≥0 => spatial L δ hδ U X ε k p ω t) := by
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
      ‖insertedWord ((level L δ hδ ε k).window p) R.totalVariance
        (fun s => U (ω,s)) (fun q => X (ω,q)) ((level L δ hδ ε k).test p) t x‖ ≤ K := by
    have hte : t ∈ Ioo ((level L δ hδ ε k).window p).left ((level L δ hδ ε k).window p).right := by
      change t ∈ Ioo R.base ((level L δ hδ ε k).terminal p)
      rw [terminal_eq L δ hδ ε 0 k p]
      exact ht
    have hHb : ∀ z,‖GaussianTaylor.hessian (GaussianItoTest.backward
        ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) z‖ ≤ B :=
      fun z => BackwardRegularity.gaussian_state_hessian_bound _
        (((level L δ hδ ε k).test_uniform.smooth p).of_le (by simp)) (hC (ε,p)) (hD (ε,p)) (hB (ε,p)) z
    have hh := inserted_pointwise_bound ((level L δ hδ ε k).window p) hAn
      (fun z => by simpa only [Real.norm_eq_abs] using hA z) hBn (fun s => U (ω,s)) (fun q => X (ω,q))
      hte (GaussianItoTest.backward ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) hHb x
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
    exact ((physical_insertion_measurable (level L δ hδ ε k) hU hX).comp
      ((measurable_const (a := ((p,ω),t))).prodMk measurable_id)).aestronglyMeasurable
  · exact fun ε => Eventually.of_forall (hb ε)
  · exact integrable_const _
  · exact Eventually.of_forall (continuous_insertedWord L δ hδ U X k p ω ht)

end SHE.RecursiveRemainderLimit
