module

public import SHE.JointWordAnalytic
public import SHE.PhysicalRemainderMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointInsertionBounds
open Set MeasureTheory StoppedFourier WordRecursion CovarianceEndpoint GaussianItoTest
open PhysicalRemainderBound PhysicalRemainderMass UniformSmooth CutoffWordLevel JointWordAnalytic
abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- Heat domination at an arbitrary old joint state. The local newest
point is V; no representation of the old state by one process is used. -/
theorem pointwise_bound {n : ℕ} (W : EndpointWindow n) {a : ℝ→ℝ}
    {A B : ℝ} (hA : 0≤A) (ha : ∀ z,|a z|≤A) (hB : 0≤B)
    (X : ℝ×HeatCircle→ℝ) {t : ℝ} (ht : t∈Ioo W.left W.right)
    (G : State n→ℝ) (z : State n) (hH : ‖GaussianTaylor.hessian G z‖≤B) (x : HeatCircle) :
    ‖WordRecursion.insertion a W.coefficient W.observations t x G
      (JointPhysicalInsertion.appendState (X (t,x)) z)‖≤
      ((1/2:ℝ)*(A+W.upper)*B)*‖heatRow W.observations t x‖^2 := by
  let H := GaussianTaylor.hessian G z
  let v := heatRow W.observations t x
  have hc : |a (X (t,x))-W.coefficient (t,x)|≤A+W.upper :=
    (abs_sub _ _).trans (add_le_add (ha _) (W.bounded t (Ioo_subset_Icc_self ht) x))
  have hh : ‖H v v‖≤B*‖v‖*‖v‖ := (GaussianTaylor.bilinear_norm_le H v v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) (norm_nonneg _))
  rw [JointPhysicalInsertion.insertion_appendState]
  change ‖(1/2:ℝ)*(a (X (t,x))-W.coefficient (t,x))*H v v‖≤_
  rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),Real.norm_eq_abs]
  have he := mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤1/2)) hh
    (norm_nonneg _) (mul_nonneg (by norm_num) (add_nonneg hA W.upper_nonneg))
  convert he using 1 <;> ring

theorem spatial_bound {n : ℕ} (W : EndpointWindow n) {a : ℝ→ℝ}
    {A B : ℝ} (hA : 0≤A) (ha : ∀ z,|a z|≤A) (hB : 0≤B)
    (X : ℝ×HeatCircle→ℝ) {t : ℝ} (ht : t∈Ioo W.left W.right)
    (G : State n→ℝ) (z : State n) (hH : ‖GaussianTaylor.hessian G z‖≤B) :
    ‖∫ x : HeatCircle,WordRecursion.insertion a W.coefficient W.observations t x G
      (JointPhysicalInsertion.appendState (X (t,x)) z) ∂AddCircle.haarAddCircle‖≤
      ((1/2:ℝ)*(A+W.upper)*B*n)*(1+heatConstant*(W.right-t)^(-(1/2:ℝ))) := by
  let K : ℝ := (1/2:ℝ)*(A+W.upper)*B
  have hK : 0≤K := mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA W.upper_nonneg)) hB
  have hi := (row_norm_square_integrable W.observations (fun i => ht.2.trans_le (W.target_after i))).const_mul K
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall
    (fun x => pointwise_bound W hA ha hB X ht G z hH x))
  rw [integral_const_mul] at hh
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (row_norm_square_mass_bound W.observations ht.2 W.target_after) hK
  convert hm using 1 <;> ring

variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

theorem remainder_bound {A B C D : ℝ} (hA : 0≤A) (ha : ∀ z,|R.totalVariance z|≤A)
    (hB : 0≤B) (hC : ∀ p z,‖L.test p z‖≤C) (hD : ∀ p z,‖fderiv ℝ (L.test p) z‖≤D)
    (hDD : ∀ p z,‖GaussianTaylor.hessian (L.test p) z‖≤B) (p : P) (ω : Ω) :
    ‖remainder L Λ U V XU XV p ω‖≤((1/2:ℝ)*(A+R.upper)*B*n)*heatMass R.horizon := by
  have hb : ‖remainder L Λ U V XU XV p ω‖≤
      ∫ t in R.base..L.terminal p,((1/2:ℝ)*(A+R.upper)*B*n)*
        (1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (L.terminal_base p) ?_
      (endpoint_majorant_integrable ((1/2:ℝ)*(A+R.upper)*B*n))
    filter_upwards [volume.ae_ne (L.terminal p)] with t ht htin
    have hW : t∈Ioo (L.window p).left (L.window p).right := ⟨htin.1,lt_of_le_of_ne htin.2 ht⟩
    exact spatial_bound (L.window p) hA ha hB (fun q => XV (ω,q)) hW
      (backward (L.window p) (L.test p) t) (state L Λ U V XU XV p ω t)
      (BackwardRegularity.gaussian_state_hessian_bound _ ((L.test_uniform.smooth p).of_le (by simp))
        (hC p) (hD p) (hDD p) _)
  rw [intervalIntegral.integral_const_mul,heat_majorant_mass (L.terminal_base p)] at hb
  have hm := heatMass_mono (sub_nonneg.mpr (L.terminal_base p))
    (by linarith [R.base_nonneg,L.terminal_horizon p] : L.terminal p-R.base≤R.horizon)
  have hK : 0≤(1/2:ℝ)*(A+R.upper)*B*n :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA R.upper_nonneg)) hB) (Nat.cast_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left hm hK)

theorem uniform_level_bound : ∃ K : ℝ,0≤K ∧ ∀ p ω,
    ‖leaf L Λ U V XU XV p ω‖≤K ∧ ‖reference L Λ U V XU XV p ω‖≤K ∧
      ‖remainder L Λ U V XU XV p ω‖≤K := by
  obtain ⟨A,hAn,hA⟩ := (UniformBoundedSmooth.fixed (P := Unit) R.totalVariance_smooth).norm_bound
  obtain ⟨C,hCn,hC⟩ := L.test_uniform.norm_bound
  obtain ⟨D,hDn,hD⟩ := L.test_uniform.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := L.test_uniform.fderiv.fderiv.norm_bound
  let K : ℝ := ((1/2:ℝ)*(A+R.upper)*B*n)*heatMass R.horizon
  have hKn : 0≤K := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hAn R.upper_nonneg)) hBn) (Nat.cast_nonneg _))
    (heatMass_nonneg (R.base_nonneg.trans R.ordered))
  refine ⟨C+K,add_nonneg hCn hKn,fun p ω => ?_⟩
  refine ⟨(hC p _).trans (le_add_of_nonneg_right hKn),?_,?_⟩
  · exact (GaussianSmooth.average_norm_bound _ (hC p) _).trans (le_add_of_nonneg_right hKn)
  · exact (remainder_bound L Λ U V XU XV hAn (fun z => by simpa only [Real.norm_eq_abs] using hA () z)
      hBn hC hD hB p ω).trans (le_add_of_nonneg_left hCn)

end SHE.JointInsertionBounds
