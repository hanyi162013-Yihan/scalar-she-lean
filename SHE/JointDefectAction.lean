module

public import SHE.JointNativeDefect
public import SHE.PositiveMatrixBounds
public import SHE.GaussianTaylorAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointDefectAction
open MeasureTheory Set Finset FiniteHaar StoppedFourier WordRecursion GaussianTaylorAverage
open scoped ENNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

/-- No positivity is assumed of the signed defect matrix. Every ordered
mixed Hessian entry is retained in the full action. -/
theorem action_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {K : ℝ} (hK : 0≤K)
    (hA : ∀ i j,|A i j|≤K) (H : State n→L[ℝ]State n→L[ℝ]ℝ) :
    ‖covarianceAction A H‖≤(n:ℝ)^2*K*‖H‖ := by
  unfold covarianceAction
  calc
    _ ≤ ∑ i : Fin n,∑ j : Fin n,‖A i j*
        H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin n,∑ _j : Fin n,K*‖H‖ := sum_le_sum (fun i _ => sum_le_sum (fun j _ => by
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul (hA i j) (PositiveMatrixBounds.bilinear_basis_bound H i j)
        (norm_nonneg _) hK))
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];ring

theorem action_measurable {P : Type*} [MeasurableSpace P] {n : ℕ}
    {A : P→Matrix (Fin n) (Fin n) ℝ} (hA : Measurable A)
    {H : P→(State n→L[ℝ]State n→L[ℝ]ℝ)} (hH : Measurable H) :
    Measurable (fun p => covarianceAction (A p) (H p)) := by
  unfold covarianceAction
  apply Finset.measurable_fun_sum
  intro i _
  apply Finset.measurable_fun_sum
  intro j _
  have hc : Continuous (fun H : State n→L[ℝ]State n→L[ℝ]ℝ =>
      H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul
    (hc.measurable.comp hH)

/-- The actual mixed physical first-defect/Hessian time integral exists
up to the terminal time, for every bounded measurable Hessian field.
This is a genuine analytic applicability statement, without a stochastic
Fubini or inverse-covariance assumption. -/
theorem action_intervalIntegrable {ell M q s : ℝ} (hell : 0<ell) {n : ℕ} {Λ : ℝ}
    (hΛ : 0≤Λ) (σ T : Fin n→ℝ) (x : Fin n→HeatCircle)
    {f g : ℝ→EllipticField ell M} (hf : Measurable f) (hg : Measurable g)
    (hqs : q≤s) (hσ : ∀ i,s≤σ i) (hT : ∀ i,s≤T i)
    {H : ℝ→(State n→L[ℝ]State n→L[ℝ]ℝ)} (hH : Measurable H)
    {B : ℝ} (hB : 0≤B) (hbound : ∀ r ∈ Icc q s,‖H r‖≤B) :
    IntervalIntegrable (fun r => covarianceAction
      (JointNativeDefect.matrix hell Λ σ T x (f r) (g r) r) (H r)) volume q s := by
  have hM : 0≤M := elliptic_upper_nonneg (f q).1 ell M hell (f q).2.2
  have hm := JointNativeDefect.measurable_comp hell Λ
    (σ := fun _ : ℝ => σ) (T := fun _ : ℝ => T) (x := fun _ : ℝ => x)
    (fun _ => measurable_const) (fun _ => measurable_const) (fun _ => measurable_const) hf hg measurable_id
  have he := action_measurable hm hH
  have hd : IntervalIntegrable (fun r => (2*(n:ℝ)^2*M*B)*(1+heatConstant*(s-r)^(-(1/2:ℝ)))) volume q s :=
    CovarianceEndpoint.endpoint_majorant_integrable _
  apply hd.mono_fun' he.aestronglyMeasurable
  rw [uIoc_of_le hqs]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne s)] with r hr hne
  have hrs : r<s := lt_of_le_of_ne hr.2 hne
  have hK : 0≤2*M*(1+heatConstant*(s-r)^(-(1/2:ℝ))) :=
    mul_nonneg (mul_nonneg (by norm_num) hM) (add_nonneg zero_le_one
      (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (sub_pos.mpr hrs).le _)))
  calc
    _ ≤ (n:ℝ)^2*(2*M*(1+heatConstant*(s-r)^(-(1/2:ℝ))))*‖H r‖ :=
      action_bound _ hK (JointNativeDefect.entry_bound hell hΛ σ T x (f r) (g r) hrs hσ hT) _
    _ ≤ (n:ℝ)^2*(2*M*(1+heatConstant*(s-r)^(-(1/2:ℝ))))*B :=
      mul_le_mul_of_nonneg_left (hbound r ⟨hr.1.le,hr.2⟩) (mul_nonneg (sq_nonneg _) hK)
    _ = _ := by ring

end SHE.JointDefectAction
