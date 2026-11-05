module

public import SHE.CutoffCarriers
public import SHE.PhysicalRemainderMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.UncutRowMass
open Set MeasureTheory Filter StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalRemainderBound PhysicalRemainderMass
open CovarianceEndpoint
open Classical
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

theorem row_eq_time (k : ℕ) (p : History P k) {t : ℝ} (ht : R.base<t ∧ t<(carrier L k).terminal p)
    (x : HeatCircle) :
    row L k (p,(t,x))=heatRow ((carrier L k).observations.observations p) t x := by
  simp only [row,Interior,ht,true_and,ite_true]
  change heatRow _ (ClippedCovariance.clip R.base ((carrier L k).terminal p) t) x=_
  rw [ClippedCovariance.clip_eq ⟨ht.1.le,ht.2.le⟩]

theorem row_zero_time (k : ℕ) (p : History P k) {t : ℝ}
    (ht : ¬(R.base<t ∧ t<(carrier L k).terminal p)) (x : HeatCircle) : row L k (p,(t,x))=0 := by
  simp only [row,Interior,ht,ite_false]

theorem row_spatial_integrable (k : ℕ) (p : History P k) (t : ℝ) :
    Integrable (fun x : HeatCircle => ‖row L k (p,(t,x))‖^2) AddCircle.haarAddCircle := by
  by_cases ht : R.base<t ∧ t<(carrier L k).terminal p
  · simp_rw [row_eq_time L k p ht]
    exact row_norm_square_integrable _ (fun i => ht.2.trans_le ((carrier L k).targets_after p i))
  · simp_rw [row_zero_time L k p ht,norm_zero,zero_pow (by omega : 2≠0)]
    exact integrable_const (0 : ℝ)

def majorant (k : ℕ) (p : History P k) : ℝ → ℝ :=
  (Ioc R.base ((carrier L k).terminal p)).indicator
    (fun t => ((n+k : ℕ) : ℝ)*(1+heatConstant*((carrier L k).terminal p-t)^(-(1/2:ℝ))))

theorem majorant_integrable (k : ℕ) (p : History P k) : Integrable (majorant L k p) volume := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact (endpoint_majorant_integrable ((n+k : ℕ) : ℝ)).1

theorem row_spatial_mass_le (k : ℕ) (p : History P k) (t : ℝ) :
    (∫ x : HeatCircle, ‖row L k (p,(t,x))‖^2 ∂AddCircle.haarAddCircle) ≤ majorant L k p t := by
  by_cases ht : R.base<t ∧ t<(carrier L k).terminal p
  · simp_rw [row_eq_time L k p ht]
    rw [majorant,indicator_of_mem (show t ∈ Ioc R.base ((carrier L k).terminal p) from ⟨ht.1,ht.2.le⟩)]
    exact row_norm_square_mass_bound _ ht.2 ((carrier L k).targets_after p)
  · simp_rw [row_zero_time L k p ht,norm_zero,zero_pow (by omega : 2≠0),integral_zero]
    exact Set.indicator_nonneg (fun t ht => mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le
        (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)))) _

theorem row_node_integrable (k : ℕ) (p : History P k) :
    Integrable (fun z : ℝ×HeatCircle => ‖row L k (p,z)‖^2) (nodeMeasure R) := by
  have hm : Measurable (fun z : ℝ×HeatCircle => ‖row L k (p,z)‖^2) :=
    (((row_measurable L k).comp (measurable_const.prodMk measurable_id)).norm).pow_const 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (row_spatial_integrable L k p),?_⟩
  have hdom := (majorant_integrable L k p).restrict (s := Ioc R.base R.horizon)
  apply hdom.mono' hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  have heq : (fun t => ∫ x : HeatCircle, ‖‖row L k (p,(t,x))‖^2‖ ∂AddCircle.haarAddCircle)=
      fun t => ∫ x : HeatCircle, ‖row L k (p,(t,x))‖^2 ∂AddCircle.haarAddCircle := by
    funext t
    apply integral_congr_ae
    filter_upwards with x
    exact Real.norm_of_nonneg (sq_nonneg _)
  filter_upwards with t
  rw [congrFun heq t]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  exact row_spatial_mass_le L k p t

theorem row_node_mass_le (k : ℕ) (p : History P k) :
    (∫ z : ℝ×HeatCircle, ‖row L k (p,z)‖^2 ∂nodeMeasure R) ≤
      ((n+k : ℕ) : ℝ)*heatMass R.horizon := by
  have hsub : Ioc R.base ((carrier L k).terminal p) ⊆ Ioc R.base R.horizon :=
    fun t ht => ⟨ht.1,ht.2.trans ((carrier L k).terminal_horizon p)⟩
  rw [show nodeMeasure R=(volume.restrict (Ioc R.base R.horizon)).prod AddCircle.haarAddCircle from rfl,
    integral_prod _ (row_node_integrable L k p)]
  have hle := integral_mono_ae ((row_node_integrable L k p).integral_prod_left)
    ((majorant_integrable L k p).restrict (s := Ioc R.base R.horizon))
    (Eventually.of_forall (row_spatial_mass_le L k p))
  have heq : (∫ t in Ioc R.base R.horizon, majorant L k p t)=
      ((n+k : ℕ) : ℝ)*heatMass ((carrier L k).terminal p-R.base) := by
    rw [majorant,integral_indicator measurableSet_Ioc,Measure.restrict_restrict_of_subset hsub,
      ← intervalIntegral.integral_of_le ((carrier L k).terminal_base p),intervalIntegral.integral_const_mul,
      heat_majorant_mass ((carrier L k).terminal_base p)]
    rfl
  rw [heq] at hle
  apply hle.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact heatMass_mono (sub_nonneg.mpr ((carrier L k).terminal_base p))
    (by linarith [(carrier L k).terminal_horizon p,R.base_nonneg])

end SHE.UncutRowMass
