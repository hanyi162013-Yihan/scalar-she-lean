module

public import SHE.NativePhysicalRowFields
public import SHE.JointDefectDomination
public import SHE.NativeObservationProcess
public import SHE.CovarianceEndpoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointNativeDefect
open MeasureTheory Set FiniteHaar StoppedFourier NativeObservationCovariance
open scoped ENNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩

/-- The literal physical first-defect matrix for arbitrary two
coefficient fields. Stops and heat targets are independent arguments. -/
def matrix {ell M : ℝ} (hell : 0<ell) {n : ℕ} (Λ : ℝ)
    (σ T : Fin n→ℝ) (x : Fin n→HeatCircle) (f g : EllipticField ell M) (r : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  let u := fun i => row hell f (T i) r (x i)
  let v := fun i => row hell g (T i) r (x i)
  let e := fun i => 1-Real.exp (-Λ*(σ i-r))
  fun i j => e i*inner ℝ (u i-v i) (v j)+e j*inner ℝ (v i) (u j-v j)+
    e i*e j*inner ℝ (u i-v i) (u j-v j)

theorem measurable_comp {P : Type*} [MeasurableSpace P] {ell M : ℝ} (hell : 0<ell)
    {n : ℕ} (Λ : ℝ) {σ T : P→Fin n→ℝ} {x : P→Fin n→HeatCircle}
    (hσ : ∀ i,Measurable (fun p => σ p i)) (hT : ∀ i,Measurable (fun p => T p i))
    (hx : ∀ i,Measurable (fun p => x p i)) {f g : P→EllipticField ell M}
    (hf : Measurable f) (hg : Measurable g) {r : P→ℝ} (hr : Measurable r) :
    Measurable (fun p => matrix hell Λ (σ p) (T p) (x p) (f p) (g p) (r p)) := by
  have hu (i) := NativePhysicalRowFields.row_measurable_comp hell hf (hT i) hr (hx i)
  have hv (i) := NativePhysicalRowFields.row_measurable_comp hell hg (hT i) hr (hx i)
  have he (i) : Measurable (fun p => 1-Real.exp (-Λ*(σ p i-r p))) :=
    measurable_const.sub (((hσ i).sub hr).const_mul (-Λ)).exp
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hinner {u v : P→RealHaarInput} (hU : Measurable u) (hV : Measurable v) :
      Measurable (fun p => inner ℝ (u p) (v p)) :=
    continuous_inner.measurable.comp (hU.prodMk hV)
  exact (((he i).mul (hinner ((hu i).sub (hv i)) (hv j))).add
    ((he j).mul (hinner (hv i) ((hu j).sub (hv j))))).add
    (((he i).mul (he j)).mul (hinner ((hu i).sub (hv i)) ((hu j).sub (hv j))))

theorem row_norm_sq_endpoint {ell M s r T : ℝ} (hell : 0<ell) (f : EllipticField ell M)
    (hrs : r<s) (hsT : s≤T) (x : HeatCircle) :
    ‖row hell f T r x‖^2≤M*(1+heatConstant*(s-r)^(-(1/2:ℝ))) := by
  have hM : 0≤M := elliptic_upper_nonneg f.1 ell M hell f.2.2
  have hp := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hrs) (sub_le_sub_right hsT r)
    (by norm_num : -(1/2:ℝ)≤0)
  exact (NativeObservationProcess.row_norm_sq_bound hell f (hrs.trans_le hsT) le_rfl x).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp heatConstant_pos.le)) hM)

/-- Uniform in damping, individual future stops, spatial centers and
both arbitrary dependent coefficients. The terminal singularity is the
integrable heat square singularity, with no extra inverse gap. -/
theorem entry_bound {ell M s r : ℝ} (hell : 0<ell) {n : ℕ} {Λ : ℝ} (hΛ : 0≤Λ)
    (σ T : Fin n→ℝ) (x : Fin n→HeatCircle) (f g : EllipticField ell M)
    (hrs : r<s) (hσ : ∀ i,s≤σ i) (hT : ∀ i,s≤T i) (i j : Fin n) :
    |matrix hell Λ σ T x f g r i j|≤2*M*(1+heatConstant*(s-r)^(-(1/2:ℝ))) := by
  have hM : 0≤M := elliptic_upper_nonneg f.1 ell M hell f.2.2
  let D : ℝ := M*(1+heatConstant*(s-r)^(-(1/2:ℝ)))
  have hD : 0≤D := mul_nonneg hM (add_nonneg zero_le_one
    (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (sub_pos.mpr hrs).le _)))
  have hu (k) : ‖row hell f (T k) r (x k)‖≤Real.sqrt D := by
    have h := row_norm_sq_endpoint hell f hrs (hT k) (x k)
    change _≤D at h
    nlinarith [Real.sq_sqrt hD,Real.sqrt_nonneg D,norm_nonneg (row hell f (T k) r (x k))]
  have hv (k) : ‖row hell g (T k) r (x k)‖≤Real.sqrt D := by
    have h := row_norm_sq_endpoint hell g hrs (hT k) (x k)
    change _≤D at h
    nlinarith [Real.sq_sqrt hD,Real.sqrt_nonneg D,norm_nonneg (row hell g (T k) r (x k))]
  have he (k) : 0≤Real.exp (-Λ*(σ k-r)) ∧ Real.exp (-Λ*(σ k-r))≤1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (by linarith [hσ k])
  have hh := JointDefectDomination.direct_abs_le (Real.sqrt_nonneg D) (he i) (he j)
    (hu i) (hu j) (hv i) (hv j)
  change |matrix hell Λ σ T x f g r i j|≤2*(Real.sqrt D)^2 at hh
  rw [Real.sq_sqrt hD] at hh
  convert hh using 1 <;> dsimp [D] <;> ring

/-- Actual time integrability reaches the terminal time even when some
heat targets equal it. Coefficients may be unrelated measurable paths. -/
theorem entry_intervalIntegrable {ell M q s : ℝ} (hell : 0<ell) {n : ℕ} {Λ : ℝ}
    (hΛ : 0≤Λ) (σ T : Fin n→ℝ) (x : Fin n→HeatCircle)
    {f g : ℝ→EllipticField ell M} (hf : Measurable f) (hg : Measurable g)
    (hqs : q≤s) (hσ : ∀ i,s≤σ i) (hT : ∀ i,s≤T i) (i j : Fin n) :
    IntervalIntegrable (fun r => matrix hell Λ σ T x (f r) (g r) r i j) volume q s := by
  have hm := measurable_comp hell Λ (σ := fun _ : ℝ => σ) (T := fun _ : ℝ => T)
    (x := fun _ : ℝ => x) (fun _ => measurable_const) (fun _ => measurable_const)
    (fun _ => measurable_const) hf hg measurable_id
  have he : Measurable (fun r => matrix hell Λ σ T x (f r) (g r) r i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hm)
  have hd : IntervalIntegrable (fun r => (2*M)*(1+heatConstant*(s-r)^(-(1/2:ℝ)))) volume q s :=
    CovarianceEndpoint.endpoint_majorant_integrable (2*M)
  apply hd.mono_fun' he.aestronglyMeasurable
  rw [uIoc_of_le hqs]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne s)] with r hr hne
  simpa only [Real.norm_eq_abs] using
    entry_bound hell hΛ σ T x (f r) (g r) (lt_of_le_of_ne hr.2 hne) hσ hT i j

end SHE.JointNativeDefect
