module
public import SHE.DependentProducts

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.GeometricIntegral
open MeasureTheory
variable {X:Type*} [MeasurableSpace X]

/-- Integral Hölder interpolation proved by normalized weighted AM-GM.
Positive caps handle zero-energy functions without dividing by energy. -/
theorem positive_caps (μ:Measure X) {f g:X→ℝ} (hf:Measurable f)(hg:Measurable g)
    (hf0:∀x,0≤f x)(hg0:∀x,0≤g x)(hfi:Integrable f μ)(hgi:Integrable g μ)
    {A B p q:ℝ}(hA:0<A)(hB:0<B)(hp:0≤p)(hq:0≤q)(hpq:p+q=1)
    (hfa:(∫x,f x ∂μ)≤A)(hgb:(∫x,g x ∂μ)≤B):
    Integrable (fun x=>(f x)^p*(g x)^q) μ ∧
      (∫x,(f x)^p*(g x)^q ∂μ)≤A^p*B^q:=by
  let C:=A^p*B^q
  have hC:0≤C:=mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
  let D:X→ℝ:=fun x=>C*(p*(f x/A)+q*(g x/B))
  have hD:Integrable D μ:=((hfi.div_const A).const_mul p |>.add ((hgi.div_const B).const_mul q)).const_mul C
  have hpoint (x:X):(f x)^p*(g x)^q≤D x:=by
    have h:=Real.geom_mean_le_arith_mean2_weighted hp hq
      (div_nonneg (hf0 x) hA.le) (div_nonneg (hg0 x) hB.le) hpq
    have he:C*((f x/A)^p*(g x/B)^q)=(f x)^p*(g x)^q:=by
      rw [Real.div_rpow (hf0 x) hA.le,Real.div_rpow (hg0 x) hB.le]
      dsimp only [C]
      field_simp [(Real.rpow_pos_of_pos hA p).ne',(Real.rpow_pos_of_pos hB q).ne']
    rw [←he]
    exact mul_le_mul_of_nonneg_left h hC
  have hi:Integrable (fun x=>(f x)^p*(g x)^q) μ:=by
    apply hD.mono' ((hf.pow_const p).mul (hg.pow_const q)).aestronglyMeasurable
    filter_upwards with x
    change ‖(f x)^p*(g x)^q‖≤D x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hf0 x) _) (Real.rpow_nonneg (hg0 x) _))]
    exact hpoint x
  refine ⟨hi,(integral_mono hi hD hpoint).trans ?_⟩
  have he:(∫x,D x ∂μ)=C*(p*((∫x,f x ∂μ)/A)+q*((∫x,g x ∂μ)/B)):=by
    dsimp only [D]
    rw [integral_const_mul,integral_add ((hfi.div_const A).const_mul p) ((hgi.div_const B).const_mul q),
      integral_const_mul,integral_const_mul,integral_div,integral_div]
  rw [he]
  have ha:(∫x,f x ∂μ)/A≤1:=(div_le_one hA).mpr hfa
  have hb:(∫x,g x ∂μ)/B≤1:=(div_le_one hB).mpr hgb
  have hh:p*((∫x,f x ∂μ)/A)+q*((∫x,g x ∂μ)/B)≤1:=by
    nlinarith [mul_le_mul_of_nonneg_left ha hp,mul_le_mul_of_nonneg_left hb hq]
  exact (mul_le_mul_of_nonneg_left hh hC).trans_eq (mul_one C)

end SHE.GeometricIntegral
