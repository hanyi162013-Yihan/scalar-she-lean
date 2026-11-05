module

public import SHE.NativeWordTimeFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Literal constant old covariance fractions on a physical interval. The
newest native reserve keeps the full original stopping history after this
fraction is subtracted. -/
namespace SHE.NativeOldFraction
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  ProfileVariance OldFractionHeatScale NativeWordTimeFields
open scoped InnerProductSpace NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

def fixedProfile (ell s h:ℝ)(p:Domain):ℝ:=if p.1∈Ioc s h then ell else 0

theorem fixedProfile_measurable (ell s h:ℝ):Measurable (fixedProfile ell s h):=
  measurable_const.ite (measurableSet_Ioc.preimage measurable_fst) measurable_const

theorem fixedProfile_bounds {ell:ℝ}(hell:0≤ell)(s h:ℝ)(p:Domain):
    0≤fixedProfile ell s h p ∧ fixedProfile ell s h p≤ell:=by
  unfold fixedProfile
  split_ifs <;> simp_all

theorem constant_variance_center (ell:ℝ){r:ℝ}(hr:0≤r)(x:HeatCircle):
    varianceMap (fun _=>ell) r x=varianceMap (fun _=>ell) r 0:=by
  unfold varianceMap
  apply intervalIntegral.integral_congr_ae_restrict
  rw[uIoc_of_le hr]
  filter_upwards[ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne r)] with t ht hn
  have htr:0<r-t:=sub_pos.mpr (lt_of_le_of_ne ht.2 hn)
  unfold varianceDensity
  rw[integral_mul_const,integral_mul_const,heatPhysical_square_mass htr,heatPhysical_square_mass htr,
    circleHeat_norm_sq_center (r-t) x 0]

/-- The scalar old fraction is exactly the translated physical interval
variance, at every original spatial center. -/
theorem old_interval_variance (ell s h:ℝ)(hsh:s<h)(x:HeatCircle):
    (∫t in s..h,ell*‖circleHeat (h-t) x‖^2)=varianceMap (fun _=>ell) (h-s) 0:=by
  have hh:=intervalIntegral.integral_comp_add_right (a:=(0:ℝ)) (b:=h-s) (fun t:ℝ=>ell*‖circleHeat (h-t) x‖^2) s
  simp only[zero_add,sub_add_cancel] at hh
  rw[←hh]
  calc
    _=varianceMap (fun _=>ell) (h-s) x:=by
      unfold varianceMap
      apply intervalIntegral.integral_congr_ae_restrict
      rw[uIoc_of_le (sub_pos.mpr hsh).le]
      filter_upwards[ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (h-s))] with t ht hn
      have htr:0<(h-s)-t:=sub_pos.mpr (lt_of_le_of_ne ht.2 hn)
      unfold varianceDensity
      rw[integral_mul_const,heatPhysical_square_mass htr]
      rw[show h-(t+s)=(h-s)-t by ring]
      ring
    _=_:=constant_variance_center ell (sub_pos.mpr hsh).le x

/-- The physical fixed profile has precisely the old interval variance. -/
theorem fixedProfile_variance (ell s h:ℝ)(hs:0≤s)(hsh:s<h)(x:HeatCircle):
    varianceMap (fixedProfile ell s h) h x=varianceMap (fun _=>ell) (h-s) 0:=by
  let F:ℝ→ℝ:=fun t=>ell*‖circleHeat (h-t) x‖^2
  have hh:0≤h:=hs.trans hsh.le
  have he:varianceMap (fixedProfile ell s h) h x=
      ∫t in (0:ℝ)..h,(Ioc s h).indicator F t:=by
    unfold varianceMap
    apply intervalIntegral.integral_congr_ae_restrict
    rw[uIoc_of_le hh]
    filter_upwards[ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne h)] with t ht hn
    have htr:0<h-t:=sub_pos.mpr (lt_of_le_of_ne ht.2 hn)
    by_cases hti:t∈Ioc s h
    · rw[Set.indicator_of_mem hti]
      unfold varianceDensity
      simp only[fixedProfile,hti,ite_true]
      rw[integral_mul_const,heatPhysical_square_mass htr]
      dsimp[F];ring
    · rw[Set.indicator_of_notMem hti]
      unfold varianceDensity
      simp only[fixedProfile,hti,ite_false,mul_zero,integral_zero]
  rw[he,intervalIntegral.integral_of_le hh,integral_indicator measurableSet_Ioc]
  have hsub:Ioc s h⊆Ioc (0:ℝ) h:=fun t ht=>⟨hs.trans_lt ht.1,ht.2⟩
  rw[Measure.restrict_restrict_of_subset hsub,←intervalIntegral.integral_of_le hsh.le]
  exact old_interval_variance ell s h hsh x

end SHE.NativeOldFraction
