module

public import SHE.ForestLeafAbsolute
public import SHE.ForestLeafMarkEnergy
public import SHE.ConditionalSquareL1

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.ForestLeafAbsoluteMass
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2 OrderedHeatForests
local instance forestLeafAbsoluteMass_period : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Quantitative ABSOLUTE old-space mass, proved before signed
averaging. This is the required envelope for original-history FTC
Fubini, and uses no cancellations. -/
theorem mass_bound {m k : ℕ} (κ : ℝ) (hκ : 0<κ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin m→HeatCircle) (j : Fin (m+k))
    (e : Ω×HeatCircle→ℝ) (he : Measurable e)
    (hei : Integrable (fun z=>|e z|^2) (μ.prod haarAddCircle))
    (F : (Ω×HeatCircle)×(Fin k→HeatCircle)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C)
    (hi : ∀ᵐ x:HeatCircle ∂haarAddCircle,∀ᵐ w:Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      Integrable (fun ω=>|F ((ω,x),w)|^2) μ)
    (hb : ∀ᵐ x:HeatCircle ∂haarAddCircle,∀ᵐ w:Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      (∫ ω,|F ((ω,x),w)|^2 ∂μ)≤C*
        (parentDensity κ hκ k t ht (values aRoot k w)*
          ScalarFibreRMS.rms μ e (x+values aRoot k w j))^2) :
    (∫ z,|F z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle)))≤
      sqrt C*(Fintype.card (Choices m k):ℝ)*sqrt (∫ z,|e z|^2 ∂μ.prod haarAddCircle) := by
  let η:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*π))
  let ν:=μ.prod (haarAddCircle (T:=2*π))
  let A:=fun z : Ω×HeatCircle=>∫ w,|F (z,w)| ∂η
  have hAbs : Measurable (fun z=>|F z|):=continuous_abs.measurable.comp hF
  have hA : Measurable A:=hAbs.stronglyMeasurable.integral_prod_right'.measurable
  have hh:=ForestLeafMarkEnergy.leaf_mark_energy μ κ hκ t ht aRoot j e he hei
    (fun z=>|F z|) hAbs C hC
    (hi.mono (fun x hx=>hx.mono (fun w hw=>by simpa only [abs_abs] using hw)))
    (hb.mono (fun x hx=>hx.mono (fun w hw=>by simpa only [abs_abs] using hw)))
  have hmem : MemLp A 2 ν:=by
    apply (memLp_two_iff_integrable_sq hA.aestronglyMeasurable).mpr
    simpa only [sq_abs] using hh.1
  have hone : MemLp (fun _ : Ω×HeatCircle=>(1:ℝ)) 2 ν:=memLp_const 1
  have hc:=integral_mul_normTwo_bound hone hmem
  have honeN : normTwo ν (fun _ : Ω×HeatCircle=>(1:ℝ))=1:=by
    simp only [normTwo,one_pow,integral_const,probReal_univ,smul_eq_mul,mul_one,sqrt_one]
  have hInt : (∫ z,A z ∂ν)≤normTwo ν A:=
    (le_abs_self _).trans (by simpa only [honeN,one_mul] using hc)
  have hNorm : normTwo ν A≤sqrt C*(Fintype.card (Choices m k):ℝ)*
      sqrt (∫ z,|e z|^2 ∂ν):=by
    have hs:=sqrt_le_sqrt hh.2
    rw [sqrt_mul (mul_nonneg hC (sq_nonneg _)),sqrt_mul hC,sqrt_sq_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _)] at hs
    simpa only [normTwo,sq_abs,A,ν,η,mul_assoc] using hs
  have hj:=ForestLeafAbsolute.joint_integrable μ κ hκ t ht aRoot j e he hei F hF C hC hi hb
  have heq : (∫ z,|F z| ∂ν.prod η)=∫ z,A z ∂ν:=by
    simpa only [A,ν,η,Real.norm_eq_abs] using integral_prod _ hj.norm
  rw [heq]
  exact hInt.trans hNorm

end SHE.ForestLeafAbsoluteMass
