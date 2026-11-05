module

public import SHE.ProfileL2
public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HolderNormTwo
open MeasureTheory ProfileL2
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- On the actual probability space, taking a Holder power contracts
the spatial L2 norm to the same power, including the zero-energy case. -/
theorem power {f : X→ℝ} (hf : MemLp f 2 μ) {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    MemLp (fun x=>|f x|^β) 2 μ ∧
      normTwo μ (fun x=>|f x|^β)≤(normTwo μ f)^β := by
  have hm : AEStronglyMeasurable (fun x=>|f x|^β) μ:=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow_const β).aestronglyMeasurable
  have hbase : (∫⁻ x,ENNReal.ofReal (‖f x‖^(2:ℝ)) ∂μ)≤
      ENNReal.ofReal ((normTwo μ f)^2) := by
    simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs]
    rw [←ofReal_integral_eq_lintegral_ofReal hf.integrable_sq (ae_of_all _ (fun _=>sq_nonneg _)),
      normTwo_sq]
  have hfrac:=FractionalMoment.moment_fraction hf.aestronglyMeasurable hβ hβ1
    (sq_nonneg (normTwo μ f)) hbase
  have he (x : X) : (|f x|^β)^2=‖f x‖^((2:ℝ)*β) := by
    rw [←Real.rpow_mul_natCast (abs_nonneg (f x)),Real.norm_eq_abs]
    congr 1
    ring
  have hbound : (∫⁻ x,ENNReal.ofReal ((|f x|^β)^2) ∂μ)≤
      ENNReal.ofReal (((normTwo μ f)^2)^β) := by
    simpa only [he] using hfrac
  have hh:=RealMomentBound.integral_bound μ (fun x=>(|f x|^β)^2)
    (hm.pow 2) (fun _=>sq_nonneg _)
    (Real.rpow_nonneg (sq_nonneg _) _) hbound
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr hh.1,?_⟩
  have hs : ((normTwo μ f)^2)^β=((normTwo μ f)^β)^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (normTwo_nonneg _ _),
      ←Real.rpow_mul_natCast (normTwo_nonneg _ _)]
    congr 1
    ring
  have hsq : (normTwo μ (fun x=>|f x|^β))^2≤((normTwo μ f)^β)^2 := by
    rw [normTwo_sq]
    exact hh.2.trans_eq hs
  exact (sq_le_sq₀ (normTwo_nonneg _ _) (Real.rpow_nonneg (normTwo_nonneg _ _) _)).mp hsq

end SHE.HolderNormTwo
