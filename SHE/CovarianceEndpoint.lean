module

public import SHE.ClippedCovariance

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.CovarianceEndpoint
open MeasureTheory Set Finset Matrix WordRecursion CovarianceMatrix ProfileVariance StoppedFourier
open scoped ENNReal Topology MatrixOrder Matrix.Norms.Elementwise
local instance covarianceEndpoint_circlePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem abs_triple_le_half_squares {c a b M : ℝ} (hM : 0 ≤ M) (hc : |c| ≤ M) :
    |c*a*b| ≤ M/2*(a^2+b^2) := by
  have hs : |a| * |b| ≤ (a^2+b^2)/2 := by
    have hh := sq_nonneg (|a|-|b|)
    rw [sub_sq,sq_abs,sq_abs] at hh
    linarith only [hh]
  calc
    _ = |c| * (|a| * |b|) := by rw [abs_mul,abs_mul]; ring
    _ ≤ M * (|a| * |b|) := mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ M*((a^2+b^2)/2) := mul_le_mul_of_nonneg_left hs hM
    _ = _ := by ring

theorem heatRow_square_integrable {n : ℕ} (Z : Fin n → Observation) {t : ℝ}
    (ht : ∀ i,t < (Z i).target) (i : Fin n) :
    Integrable (fun x : HeatCircle => (heatRow Z t x i)^2) AddCircle.haarAddCircle := by
  have he : (fun x : HeatCircle => (heatRow Z t x i)^2)=
      fun x => ‖heatPhysical ((Z i).target-t) (Z i).center x‖^2 := by
    funext x
    exact heatPhysical_re_sq (sub_pos.mpr (ht i)) _ _
  rw [he]
  exact heatPhysical_square_integrable (sub_pos.mpr (ht i)) _

theorem heatRow_square_mass {n : ℕ} (Z : Fin n → Observation) {t : ℝ}
    (ht : ∀ i,t < (Z i).target) (i : Fin n) :
    (∫ x : HeatCircle,(heatRow Z t x i)^2 ∂AddCircle.haarAddCircle)=
      ‖circleHeat ((Z i).target-t) (Z i).center‖^2 := by
  have he : (fun x : HeatCircle => (heatRow Z t x i)^2)=
      fun x => ‖heatPhysical ((Z i).target-t) (Z i).center x‖^2 := by
    funext x
    exact heatPhysical_re_sq (sub_pos.mpr (ht i)) _ _
  rw [he,heatPhysical_square_mass (sub_pos.mpr (ht i))]

theorem covarianceDensity_cross_bound {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {M s t : ℝ} (hM : 0 ≤ M)
    (ht : t < s) (hgap : ∀ i,s ≤ (Z i).target) (hbound : ∀ x,|c (t,x)| ≤ M)
    (i j : Fin n) :
    |covarianceDensity c Z t i j| ≤ M/2*
      (‖circleHeat ((Z i).target-t) (Z i).center‖^2+
        ‖circleHeat ((Z j).target-t) (Z j).center‖^2) := by
  have htarget (i : Fin n) : t < (Z i).target := ht.trans_le (hgap i)
  have hi := covariance_spatial_integrable c hc Z (sub_pos.mpr ht) hM
    (fun i => by linarith [hgap i]) (le_rfl : t ≤ t) hbound i j
  have hsq := ((heatRow_square_integrable Z htarget i).add
    (heatRow_square_integrable Z htarget j)).const_mul (M/2)
  have hb (x : HeatCircle) : ‖c (t,x)*heatRow Z t x i*heatRow Z t x j‖ ≤
      M/2*((heatRow Z t x i)^2+(heatRow Z t x j)^2) := by
    rw [Real.norm_eq_abs]
    exact abs_triple_le_half_squares hM (hbound x)
  change ‖∫ x : HeatCircle,c (t,x)*heatRow Z t x i*heatRow Z t x j ∂AddCircle.haarAddCircle‖ ≤ _
  calc
    _ ≤ ∫ x : HeatCircle,‖c (t,x)*heatRow Z t x i*heatRow Z t x j‖ ∂AddCircle.haarAddCircle :=
      by
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : HeatCircle,M/2*((heatRow Z t x i)^2+(heatRow Z t x j)^2) ∂AddCircle.haarAddCircle :=
      by
        exact integral_mono hi.norm hsq hb
    _ = _ := by
      rw [integral_const_mul,integral_add (heatRow_square_integrable Z htarget i)
        (heatRow_square_integrable Z htarget j),heatRow_square_mass Z htarget i,
        heatRow_square_mass Z htarget j]

/-- The cross covariance density has the integrable heat-square
singularity, even when an observation target is the terminal time. -/
theorem covarianceDensity_endpoint_bound {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {M s t : ℝ} (hM : 0 ≤ M)
    (ht : t < s) (hgap : ∀ i,s ≤ (Z i).target) (hbound : ∀ x,|c (t,x)| ≤ M)
    (i j : Fin n) :
    |covarianceDensity c Z t i j| ≤ M*(1+heatConstant*(s-t)^(-(1/2:ℝ))) := by
  have hh (i : Fin n) : ‖circleHeat ((Z i).target-t) (Z i).center‖^2 ≤
      1+heatConstant*(s-t)^(-(1/2:ℝ)) := by
    have hage : 0 < (Z i).target-t := by linarith [hgap i]
    apply (circleHeat_norm_sq_bound hage _).trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ heatConstant_pos.le
    exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ht) (by linarith [hgap i]) (by norm_num)
  apply (covarianceDensity_cross_bound c hc Z hM ht hgap hbound i j).trans
  calc
    _ ≤ M/2*((1+heatConstant*(s-t)^(-(1/2:ℝ)))+(1+heatConstant*(s-t)^(-(1/2:ℝ)))) :=
      mul_le_mul_of_nonneg_left (add_le_add (hh i) (hh j)) (by positivity)
    _ = _ := by ring

theorem endpoint_majorant_integrable {q s : ℝ} (M : ℝ) :
    IntervalIntegrable (fun t : ℝ => M*(1+heatConstant*(s-t)^(-(1/2:ℝ)))) volume q s := by
  have hi : IntervalIntegrable (fun t : ℝ => t^(-(1/2:ℝ))) volume 0 (s-q) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hh : IntervalIntegrable (fun t : ℝ => (s-t)^(-(1/2:ℝ))) volume q s := by
    simpa only [sub_self,sub_sub_cancel,sub_zero] using (hi.comp_sub_left s).symm
  exact (intervalIntegrable_const.add (hh.const_mul heatConstant)).const_mul M

theorem covariance_entry_intervalIntegrable_endpoint {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {M q s : ℝ} (hM : 0 ≤ M)
    (hqs : q ≤ s) (hgap : ∀ i,s ≤ (Z i).target)
    (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M) (i j : Fin n) :
    IntervalIntegrable (fun t => covarianceDensity c Z t i j) volume q s := by
  apply (endpoint_majorant_integrable (q := q) (s := s) M).mono_fun'
  · exact (covarianceDensity_measurable c hc Z i j).aestronglyMeasurable
  · rw [uIoc_of_le hqs]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    rw [Real.norm_eq_abs]
    exact covarianceDensity_endpoint_bound c hc Z hM (lt_of_le_of_ne ht.2 hts) hgap
      (hbound t ⟨ht.1.le,ht.2⟩) i j

theorem covariance_posSemidef_endpoint {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {M q s : ℝ} (hM : 0 ≤ M)
    (hqs : q ≤ s) (hgap : ∀ i,s ≤ (Z i).target)
    (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M)
    (hnonneg : ∀ t ∈ Icc q s,∀ x,0 ≤ c (t,x)) : (covariance c Z q s).PosSemidef := by
  have hi (i j : Fin n) := (covariance_entry_intervalIntegrable_endpoint c hc Z hM hqs hgap hbound i j).1
  have hh := entry_integral_posSemidef (volume.restrict (Ioc q s))
    (fun t => densityMatrix c Z t)
    (fun i j => by
      change IntegrableOn (fun t => covarianceDensity c Z t i j) (Ioc q s) volume
      simpa only [uIoc_of_le hqs] using hi i j) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
      have hts' : t < s := lt_of_le_of_ne ht.2 hts
      exact covarianceDensity_posSemidef c hc Z (sub_pos.mpr hts') hM
        (fun i => by linarith [hgap i]) (le_rfl : t ≤ t)
        (hbound t ⟨ht.1.le,ht.2⟩) (hnonneg t ⟨ht.1.le,ht.2⟩))
  have he : covariance c Z q s=(fun i j => ∫ t in Ioc q s,densityMatrix c Z t i j) := by
    ext i j
    exact intervalIntegral.integral_of_le hqs
  rwa [he]

end SHE.CovarianceEndpoint
