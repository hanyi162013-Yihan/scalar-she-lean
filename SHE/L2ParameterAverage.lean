module
public import SHE.LpOperatorParameterAverage
public import SHE.ProfileL2
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.L2ParameterAverage
open MeasureTheory
open scoped ENNReal
variable {X P C:Type*} [MeasurableSpace X][MeasurableSpace P]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][CompleteSpace C]

theorem norm_integral_sq (η:Measure X)[IsProbabilityMeasure η]
    (F:X→C)(hF:MemLp F 2 η):
    ‖∫x,F x ∂η‖^2≤∫x,‖F x‖^2 ∂η:=by
  have hc:=ProfileL2.integral_mul_normTwo_bound hF.norm
    (memLp_const (1:ℝ):MemLp (fun _:X=>(1:ℝ)) 2 η)
  have hOne:ProfileL2.normTwo η (fun _:X=>(1:ℝ))=1:=by simp [ProfileL2.normTwo]
  simp only [mul_one,hOne] at hc
  have hb:‖∫x,F x ∂η‖≤ProfileL2.normTwo η (fun x=>‖F x‖):=
    (norm_integral_le_integral_norm _).trans ((le_abs_self _).trans hc)
  exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq (ProfileL2.normTwo_sq _ _)

/-- A genuine joint square-integrable kernel has an actual L2
parameter average. No separability of the receiving probability L2
space is required. -/
theorem memLp (η:Measure X)[IsProbabilityMeasure η](ν:Measure P)[SFinite ν]
    (F:X×P→C)(hF:StronglyMeasurable F)(h2:Integrable (fun z=>‖F z‖^2) (η.prod ν)):
    MemLp (fun p=>∫x,F (x,p) ∂η) 2 ν:=by
  have hm:StronglyMeasurable (fun p=>∫x,F (x,p) ∂η):=hF.integral_prod_left'
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply h2.integral_prod_right.mono' (hm.norm.pow 2).aestronglyMeasurable
  filter_upwards [h2.prod_left_ae] with p hp
  change ‖‖∫x,F (x,p) ∂η‖^2‖≤∫x,‖F (x,p)‖^2 ∂η
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact norm_integral_sq η _ ((memLp_two_iff_integrable_sq_norm
    ((hF.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)).mpr hp)

def value (η:Measure X)[IsProbabilityMeasure η](ν:Measure P)[SFinite ν]
    (F:X×P→C)(hF:StronglyMeasurable F)(h2:Integrable (fun z=>‖F z‖^2) (η.prod ν)):
    Lp C 2 ν:=(memLp η ν F hF h2).toLp (fun p=>∫x,F (x,p) ∂η)

theorem value_ae (η:Measure X)[IsProbabilityMeasure η](ν:Measure P)[SFinite ν]
    (F:X×P→C)(hF:StronglyMeasurable F)(h2:Integrable (fun z=>‖F z‖^2) (η.prod ν)):
    value η ν F hF h2=ᵐ[ν] fun p=>∫x,F (x,p) ∂η:=
  (memLp η ν F hF h2).coeFn_toLp
end SHE.L2ParameterAverage
