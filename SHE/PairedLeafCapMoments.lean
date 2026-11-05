module

public import SHE.FractionalMoment
public import SHE.RealMomentBound
public import SHE.RoughLeafOffsetMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PairedLeafCapMoments
open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Endpoint caps may be dependent. A fractional cap moment keeps the
complementary rough degree and only an AFFINE dependence on both full
endpoint moment constants. This is what permits genuine conditional
past-offset averaging after the common-law paired comparison. -/
theorem fractional_even_moment (f g : Ω→ℝ) (hf : Measurable f) (hg : Measurable g)
    (p : ℕ) {s C0 C1 S : ℝ} (hs : 0≤s) (hs1 : s≤1)
    (hC0 : 0≤C0) (hC1 : 0≤C1) (hS : 0≤S)
    (hfi : Integrable (fun ω=>|f ω|^(2*p)) μ)
    (hgi : Integrable (fun ω=>|g ω|^(2*p)) μ)
    (hfb : (∫ ω,|f ω|^(2*p) ∂μ)≤C0*S^(2*p))
    (hgb : (∫ ω,|g ω|^(2*p) ∂μ)≤C1*S^(2*p)) :
    Integrable (fun ω=>((|f ω|+|g ω|)^s)^(2*p)) μ ∧
      (∫ ω,((|f ω|+|g ω|)^s)^(2*p) ∂μ)≤
        (1+(2:ℝ)^(2*p-1)*(C0+C1))*(S^s)^(2*p) := by
  let cap:=fun ω=>|f ω|+|g ω|
  let R:=(2:ℝ)^(2*p-1)*(C0+C1)
  have hcap0 (ω : Ω) : 0≤cap ω:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hcapm : Measurable cap:=hf.norm.add hg.norm
  have hR : 0≤R:=mul_nonneg (by positivity) (add_nonneg hC0 hC1)
  have hpoint (ω : Ω) : cap ω^(2*p)≤(2:ℝ)^(2*p-1)*(|f ω|^(2*p)+|g ω|^(2*p)) :=
    add_pow_le (abs_nonneg _) (abs_nonneg _) (2*p)
  have hcapI : Integrable (fun ω=>cap ω^(2*p)) μ :=
    ((hfi.add hgi).const_mul ((2:ℝ)^(2*p-1))).mono'
      (hcapm.pow_const _).aestronglyMeasurable
      (ae_of_all _ (fun ω=>by
        rw [Real.norm_of_nonneg (pow_nonneg (hcap0 ω) _)]
        exact hpoint ω))
  have hcapBound : (∫ ω,cap ω^(2*p) ∂μ)≤R*S^(2*p) := by
    have hh:=integral_mono hcapI ((hfi.add hgi).const_mul ((2:ℝ)^(2*p-1))) hpoint
    rw [integral_const_mul] at hh
    simp only [Pi.add_apply] at hh
    rw [integral_add hfi hgi] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add hfb hgb)
      (show 0≤(2:ℝ)^(2*p-1) by positivity)).trans_eq (by dsimp [R];ring))
  have hLin : (∫⁻ ω,ENNReal.ofReal (‖cap ω‖^(((2*p:ℕ):ℝ))) ∂μ)≤ENNReal.ofReal (R*S^(2*p)) := by
    have he (ω : Ω) : ‖cap ω‖^(((2*p:ℕ):ℝ))=cap ω^(2*p) := by
      rw [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (hcap0 ω)]
    simp_rw [he]
    rw [←ofReal_integral_eq_lintegral_ofReal hcapI (ae_of_all _ (fun ω=>pow_nonneg (hcap0 ω) _))]
    exact ENNReal.ofReal_le_ofReal hcapBound
  have hh:=FractionalMoment.moment_fraction hcapm.aestronglyMeasurable hs hs1
    (mul_nonneg hR (pow_nonneg hS _)) hLin
  have he (ω : Ω) : ‖cap ω‖^((((2*p:ℕ):ℝ))*s)=(cap ω^s)^(2*p) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hcap0 ω),←Real.rpow_mul_natCast (hcap0 ω)]
    congr 1
    ring
  simp_rw [he] at hh
  have hMi:=RealMomentBound.integral_bound μ (fun ω=>(cap ω^s)^(2*p))
    ((hcapm.pow_const s).pow_const (2*p)).aestronglyMeasurable
    (fun ω=>pow_nonneg (rpow_nonneg (hcap0 ω) _) _) (rpow_nonneg (mul_nonneg hR (pow_nonneg hS _)) _) hh
  refine ⟨hMi.1,hMi.2.trans ?_⟩
  have hRp : R^s≤1+R := by
    rcases le_total R 1 with hr|hr
    · exact (rpow_le_one hR hr hs).trans (by linarith)
    · exact (rpow_le_self_of_one_le hr hs1).trans (by linarith)
  have heS : (R*S^(2*p))^s=R^s*(S^s)^(2*p) := by
    rw [mul_rpow hR (pow_nonneg hS _),←rpow_natCast_mul hS,
      ←rpow_mul_natCast hS]
    congr 1
    ring
  rw [heS]
  exact mul_le_mul_of_nonneg_right hRp (pow_nonneg (rpow_nonneg hS _) _)

end SHE.PairedLeafCapMoments
