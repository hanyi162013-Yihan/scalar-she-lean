module

public import SHE.ScalarApproximationDiscrepancy
public import SHE.JointInsertionBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ApproximateCoefficientInsertion
open Set MeasureTheory AddCircle StoppedFourier WordRecursion GaussianItoTest CovarianceEndpoint
open SmoothApproximation ScalarData PhysicalRemainderBound PhysicalRemainderMass
abbrev State (n : ℕ) := WordRecursion.State n
local instance approximateCoefficientInsertion_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

def smoothTotal (D : ScalarData) (j : ℕ) (z : ℝ) : ℝ :=
  (ScalarReduction.additiveAmplitude D.lower)^2+D.smoothCoefficient j z

def originalTotal (D : ScalarData) (z : ℝ) : ℝ := (D.coefficient z)^2

theorem total_error (D : ScalarData) (j : ℕ) (z : ℝ) :
    |originalTotal D z-smoothTotal D j z|≤ScalarApproximationDiscrepancy.scalarError D j := by
  rw [originalTotal,←D.variance_split,smoothTotal,add_sub_add_left_eq_sub]
  exact ScalarApproximationDiscrepancy.coefficient_error D j z

/-- The extra physical insertion is the coefficient discrepancy at the
ACTUAL newest state. No Gaussian averaging of this newest factor is
introduced. Both functions are total variances, including the same
additive variance. -/
def error {n : ℕ} (D : ScalarData) (j : ℕ) (W : EndpointWindow n)
    (F : State n→ℝ) (X : ℝ×HeatCircle→ℝ) (Y : ℝ→State n) (t : ℝ) (x : HeatCircle) : ℝ :=
  (1/2:ℝ)*(originalTotal D (X (t,x))-smoothTotal D j (X (t,x)))*
    GaussianTaylor.hessian (backward W F t) (Y t) (heatRow W.observations t x) (heatRow W.observations t x)

theorem insertion_eq_approx_add_error {n : ℕ} (D : ScalarData) (j : ℕ) (W : EndpointWindow n)
    (F : State n→ℝ) (X : ℝ×HeatCircle→ℝ) (Y : ℝ→State n) (t : ℝ) (x : HeatCircle) :
    insertion (originalTotal D) W.coefficient W.observations t x (backward W F t)
      (JointPhysicalInsertion.appendState (X (t,x)) (Y t))=
    insertion (smoothTotal D j) W.coefficient W.observations t x (backward W F t)
      (JointPhysicalInsertion.appendState (X (t,x)) (Y t))+error D j W F X Y t x := by
  simp only [JointPhysicalInsertion.insertion_appendState,error]
  ring

theorem point_bound {n : ℕ} (D : ScalarData) (j : ℕ) (W : EndpointWindow n)
    (F : State n→ℝ) (X : ℝ×HeatCircle→ℝ) (Y : ℝ→State n) {B : ℝ} (hB : 0≤B)
    (t : ℝ) (hH : ‖GaussianTaylor.hessian (backward W F t) (Y t)‖≤B) (x : HeatCircle) :
    ‖error D j W F X Y t x‖≤
      ((1/2:ℝ)*ScalarApproximationDiscrepancy.scalarError D j*B)*‖heatRow W.observations t x‖^2 := by
  let H:=GaussianTaylor.hessian (backward W F t) (Y t)
  let v:=heatRow W.observations t x
  have hc:=total_error D j (X (t,x))
  have hh : ‖H v v‖≤B*‖v‖*‖v‖ := (GaussianTaylor.bilinear_norm_le H v v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) (norm_nonneg _))
  change ‖(1/2:ℝ)*(originalTotal D (X (t,x))-smoothTotal D j (X (t,x)))*H v v‖≤_
  rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),Real.norm_eq_abs]
  have he:=mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤1/2)) hh
    (norm_nonneg _) (mul_nonneg (by norm_num) (ScalarApproximationDiscrepancy.scalarError_nonneg D j))
  convert he using 1 <;> ring

theorem spatial_bound {n : ℕ} (D : ScalarData) (j : ℕ) (W : EndpointWindow n)
    (F : State n→ℝ) (X : ℝ×HeatCircle→ℝ) (Y : ℝ→State n) {B : ℝ} (hB : 0≤B)
    {t : ℝ} (ht : t∈Ioo W.left W.right)
    (hH : ‖GaussianTaylor.hessian (backward W F t) (Y t)‖≤B) :
    ‖∫x:HeatCircle,error D j W F X Y t x ∂haarAddCircle‖≤
      ((1/2:ℝ)*ScalarApproximationDiscrepancy.scalarError D j*B*n)*
        (1+heatConstant*(W.right-t)^(-(1/2:ℝ))) := by
  let K:ℝ:=(1/2:ℝ)*ScalarApproximationDiscrepancy.scalarError D j*B
  have hK : 0≤K := mul_nonneg
    (mul_nonneg (by norm_num) (ScalarApproximationDiscrepancy.scalarError_nonneg D j)) hB
  have hi:=(row_norm_square_integrable W.observations
    (fun i=>ht.2.trans_le (W.target_after i))).const_mul K
  have hh:=norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall
    (fun x=>point_bound D j W F X Y hB t hH x))
  rw [integral_const_mul] at hh
  exact hh.trans (by
    have hm:=mul_le_mul_of_nonneg_left (row_norm_square_mass_bound W.observations ht.2 W.target_after) hK
    convert hm using 1 <;> ring)

/-- The actual space-time insertion error has an integrable terminal
heat singularity. Its constant depends only on the root Hessian bound,
the finite dimension and the original time span. -/
theorem time_bound {n : ℕ} (D : ScalarData) (j : ℕ) (W : EndpointWindow n)
    (F : State n→ℝ) (X : ℝ×HeatCircle→ℝ) (Y : ℝ→State n)
    (hF : ContDiff ℝ 2 F) {C L B : ℝ} (hB : 0≤B)
    (hC : ∀z,‖F z‖≤C) (hL : ∀z,‖fderiv ℝ F z‖≤L)
    (hH : ∀z,‖GaussianTaylor.hessian F z‖≤B) :
    ‖∫t in W.left..W.right,∫x:HeatCircle,error D j W F X Y t x ∂haarAddCircle‖≤
      ((1/2:ℝ)*ScalarApproximationDiscrepancy.scalarError D j*B*n)*heatMass (W.right-W.left) := by
  have hb : ‖∫t in W.left..W.right,∫x:HeatCircle,error D j W F X Y t x ∂haarAddCircle‖≤
      ∫t in W.left..W.right,((1/2:ℝ)*ScalarApproximationDiscrepancy.scalarError D j*B*n)*
        (1+heatConstant*(W.right-t)^(-(1/2:ℝ))) := by
    apply intervalIntegral.norm_integral_le_of_norm_le W.ordered ?_
      (CovarianceEndpoint.endpoint_majorant_integrable _)
    filter_upwards [volume.ae_ne W.right] with t hne ht
    have htin:t∈Ioo W.left W.right:=⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
    exact spatial_bound D j W F X Y hB htin
      (BackwardRegularity.gaussian_state_hessian_bound _ hF hC hL hH _)
  rw [intervalIntegral.integral_const_mul,heat_majorant_mass W.ordered] at hb
  exact hb

end SHE.ApproximateCoefficientInsertion
