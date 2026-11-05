module
public import SHE.NativeRowProductEnergy
public import SHE.ScalarHeatCompleteGamma
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeRowEnergyCast
open Set MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance nativeRowEnergyCast_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeRowEnergyCast_sigma : MeasurableSpace CircleL2:=borel _
local instance nativeRowEnergyCast_borel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeRowEnergyCast_second : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {T Ω:Type*} [MeasurableSpace T] [MeasurableSpace Ω]
variable (μ:Measure Ω) [IsProbabilityMeasure μ]

theorem row_bound (F:(T×Ω)×HeatCircle→ℂ) (hF:Measurable F) {B:ℝ}
    (hB:0≤B) (hb:∀p x,‖F (p,x)‖≤B) (p:T×Ω):‖NativeRandomRows.nativeRow F p‖≤B:=by
  have hh:∀ᵐx∂haarAddCircle,‖NativeRandomRows.nativeRow F p x‖≤B:=
    (NativeRandomRows.nativeRow_ae hF hb p).mono (fun x hx=>by rw [hx];exact hb p x)
  simpa only [measureUnivNNReal,measure_univ,ENNReal.toNNReal_one,NNReal.coe_one,Real.one_rpow,one_mul] using
    Lp.norm_le_of_ae_bound hB hh

/-- Every actual bounded scalar row difference has genuine original
sample L2 integrability, before the time integral is cast to ENNReal. -/
theorem integrable (F G:(T×Ω)×HeatCircle→ℂ) (hF:Measurable F) (hG:Measurable G)
    {B:ℝ} (hB:0≤B) (hbF:∀p x,‖F (p,x)‖≤B) (hbG:∀p x,‖G (p,x)‖≤B) (t:T):
    Integrable (fun ω=>‖NativeRandomRows.nativeRow F (t,ω)-NativeRandomRows.nativeRow G (t,ω)‖^2) μ:=by
  have hm:Measurable (fun ω=>‖NativeRandomRows.nativeRow F (t,ω)-NativeRandomRows.nativeRow G (t,ω)‖^2):=
    ((((NativeRandomRows.nativeRow_measurable hF hbF).comp (measurable_const.prodMk measurable_id)).sub
      ((NativeRandomRows.nativeRow_measurable hG hbG).comp (measurable_const.prodMk measurable_id))).norm).pow_const 2
  apply (integrable_const ((2*B)^2)).mono' hm.aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sub_le _ _).trans ((add_le_add (row_bound F hF hB hbF (t,ω))
      (row_bound G hG hB hbG (t,ω))).trans_eq (by ring))) 2

/-- Exact sample cast for the positive slot density. No upper bound
or loss of correlation is introduced by changing integral conventions. -/
theorem sample (F G:(T×Ω)×HeatCircle→ℂ) (hF:Measurable F) (hG:Measurable G)
    {B K:ℝ} (hB:0≤B) (hbF:∀p x,‖F (p,x)‖≤B) (hbG:∀p x,‖G (p,x)‖≤B) (hK:0≤K) (t:T):
    (∫⁻ω,ENNReal.ofReal (K*‖NativeRandomRows.nativeRow F (t,ω)-NativeRandomRows.nativeRow G (t,ω)‖^2) ∂μ)=
      ENNReal.ofReal (K*(∫ω,‖NativeRandomRows.nativeRow F (t,ω)-NativeRandomRows.nativeRow G (t,ω)‖^2 ∂μ)):=by
  have hi:=integrable μ F G hF hG hB hbF hbG t
  rw [←ofReal_integral_eq_lintegral_ofReal (hi.const_mul K)
    (ae_of_all _ (fun _=>mul_nonneg hK (sq_nonneg _))),integral_const_mul]

/-- Exact positive time/sample cast for a literal native row slot,
using its proved time integrability and preserving the original mean. -/
theorem time (F G:(T×Ω)×HeatCircle→ℂ) (hF:Measurable F) (hG:Measurable G)
    {B:ℝ} (hB:0≤B) (hbF:∀p x,‖F (p,x)‖≤B) (hbG:∀p x,‖G (p,x)‖≤B)
    (clock:ℝ→T) {h ρ:ℝ}
    (hi:IntegrableOn (fun τ=>τ^(ρ-1/2)*(∫ω,‖NativeRandomRows.nativeRow F (clock τ,ω)-
      NativeRandomRows.nativeRow G (clock τ,ω)‖^2 ∂μ)) (Ioc (0:ℝ) h)):
    (∫⁻τ in Ioc (0:ℝ) h,∫⁻ω,ENNReal.ofReal (τ^(ρ-1/2)*
      ‖NativeRandomRows.nativeRow F (clock τ,ω)-NativeRandomRows.nativeRow G (clock τ,ω)‖^2) ∂μ)=
      ENNReal.ofReal (∫τ in Ioc (0:ℝ) h,τ^(ρ-1/2)*
        (∫ω,‖NativeRandomRows.nativeRow F (clock τ,ω)-NativeRandomRows.nativeRow G (clock τ,ω)‖^2 ∂μ)):=by
  calc
    _=(∫⁻τ in Ioc (0:ℝ) h,ENNReal.ofReal (τ^(ρ-1/2)*
        (∫ω,‖NativeRandomRows.nativeRow F (clock τ,ω)-NativeRandomRows.nativeRow G (clock τ,ω)‖^2 ∂μ))):=by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ ht
      exact sample μ F G hF hG hB hbF hbG (Real.rpow_nonneg ht.1.le _) (clock τ)
    _=_:=(ofReal_integral_eq_lintegral_ofReal hi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ ht
      exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (integral_nonneg (fun _=>sq_nonneg _)))).symm
end SHE.NativeRowEnergyCast
