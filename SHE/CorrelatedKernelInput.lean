module

public import SHE.CorrelatedKernelRMS
public import SHE.NativeRandomKernel
public import SHE.HilbertFiniteAverage
public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.CorrelatedLinearInput
open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal

theorem fractional_mass {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (e : X→ℝ) (hm : Measurable e) (hi : Integrable e ν) (h0 : ∀ x,0≤e x)
    {α : ℝ} (hα : 0≤α) (hα1 : α≤1) :
    Integrable (fun x=>e x^α) ν ∧ (∫ x,e x^α ∂ν)≤(∫ x,e x ∂ν)^α := by
  have hc : 0≤∫ x,e x ∂ν := integral_nonneg h0
  have hb : (∫⁻ x,ENNReal.ofReal (‖e x‖^(1:ℝ)) ∂ν)≤ENNReal.ofReal (∫ x,e x ∂ν) := by
    simp only [Real.rpow_one,Real.norm_of_nonneg (h0 _)]
    exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0)).symm.le
  have hh := FractionalMoment.moment_fraction hm.aestronglyMeasurable hα hα1 hc hb
  simp only [Real.norm_of_nonneg (h0 _),one_mul] at hh
  exact RealMomentBound.integral_bound ν _
    (hm.pow_const α).aestronglyMeasurable (fun x=>rpow_nonneg (h0 x) α)
    (rpow_nonneg hc α) hh

theorem sqrt_mul_power {C e α : ℝ} (hC : 0≤C) (he : 0≤e) :
    Real.sqrt (C*e^α)=Real.sqrt C*e^(α/2) := by
  rw [Real.sqrt_mul hC]
  congr 1
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul he]
  congr 1
  ring

end SHE.CorrelatedLinearInput

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance correlatedKernelInput_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance correlatedKernelInput_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance correlatedKernelInput_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance correlatedKernelInput_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance correlatedKernelInput_nativeSecondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual random integral operator applied to its dependent random
input. Higher moments are consumed pointwise before spatial Minkowski;
the surviving smallness is the true global input second moment. -/
theorem correlated_input_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω×(HeatCircle×HeatCircle)→ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0≤B) (hb : ∀ ω y x,‖F (ω,(y,x))‖≤B)
    (D : Ω×HeatCircle→ℝ) (hD : Measurable D)
    (v : Ω→CircleL2) (hv : ∀ ω,(v ω : HeatCircle→ℂ)=ᵐ[haarAddCircle] fun y=>(D (ω,y):ℂ))
    (hD2 : ∀ y,MemLp (fun ω=>D (ω,y)) 2 μ)
    (hiD2 : Integrable (fun y=>∫ ω,D (ω,y)^2 ∂μ) haarAddCircle)
    {Λ ρ t A χ CD CG : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hA : 0<A)
    (center : HeatCircle→HeatCircle)
    (hχ0 : 0≤χ) (hχ1 : χ<1) (hCD : 0≤CD) (hCG : 0≤CG)
    (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (hiDh : ∀ y,Integrable (fun ω=>|D (ω,y)|^((4*(p:ℝ))*(1-χ))) μ)
    (hbDh : ∀ y,(∫ ω,|D (ω,y)|^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD)
    (hheat : ∀ y x,0<‖ProfileVariance.heatPhysical (8*t) (center y) x‖)
    (hMom : ∀ᵐ z : HeatCircle×HeatCircle ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      Integrable (fun ω=>(‖F (ω,z)‖/(A*‖ProfileVariance.heatPhysical (8*t) (center z.1) z.2‖))^(4*p)) μ ∧
      (∫ ω,(‖F (ω,z)‖/(A*‖ProfileVariance.heatPhysical (8*t) (center z.1) z.2‖))^(4*p) ∂μ)≤CG) :
    let C := GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*A^2*((CD+CG)/2)^(1/(p:ℝ))
    Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2 ∂μ)≤
        C*(∫ y,∫ ω,D (ω,y)^2 ∂μ ∂haarAddCircle)^χ := by
  intro C
  let e : HeatCircle→ℝ := fun y=>∫ ω,D (ω,y)^2 ∂μ
  have he0 (y : HeatCircle) : 0≤e y := integral_nonneg (fun ω=>sq_nonneg _)
  have hem : Measurable e := (hD.pow_const (2:ℕ)).stronglyMeasurable.integral_prod_left'.measurable
  have hC : 0≤C := by
    dsimp only [C]
    have htr := GaussianNegativePacket.traceConstant_pos
    have hg := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
    have hc := (NativeHeatSpan.clock_pos ht).le
    unfold GaussianNegativePacket.constant
    positivity
  let W : HeatCircle×Ω→CircleL2 := fun z=>(D (z.2,z.1):ℂ) • negativeColumn Λ ρ hΛ hρ.le F (z.2,z.1)
  have hW : Measurable W :=
    ((Complex.continuous_ofReal.measurable.comp hD).comp measurable_swap).smul
      ((negativeColumn_measurable hΛ hρ.le hF hb).comp measurable_swap)
  have hWe (y : HeatCircle) (ω : Ω) : W (y,ω)=
      OneInputOperator.besselHalf Λ ρ hΛ hρ.le
        (NativeRandomRows.nativeRow (fun z : Ω×HeatCircle=>F (z.1,(y,z.2))*(D (z.1,y):ℂ)) ω) := by
    have hFy : Measurable (fun z : Ω×HeatCircle=>F (z.1,(y,z.2))) :=
      hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have hDy : Measurable (fun ω=>D (ω,y)) := hD.comp (measurable_id.prodMk measurable_const)
    have hprod : Measurable (fun z : Ω×HeatCircle=>F (z.1,(y,z.2))*(D (z.1,y):ℂ)) :=
      hFy.mul (Complex.continuous_ofReal.measurable.comp (hDy.comp measurable_fst))
    have hbound (ω : Ω) (x : HeatCircle) : ‖F (ω,(y,x))*(D (ω,y):ℂ)‖≤B*|D (ω,y)| := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb ω y x) (abs_nonneg _)
    have hr : NativeRandomRows.nativeRow
        (fun z : Ω×HeatCircle=>F (z.1,(y,z.2))*(D (z.1,y):ℂ)) ω=
        (D (ω,y):ℂ) • column F (ω,y) := by
      apply Lp.ext
      filter_upwards [NativeRandomRows.nativeRow_ae_cap hprod
        (fun ω=>B*|D (ω,y)|) hbound ω,column_ae hF hb ω y,
        Lp.coeFn_smul (D (ω,y):ℂ) (column F (ω,y))] with x hx hy hz
      rw [hx,hz,Pi.smul_apply,smul_eq_mul,hy]
      exact mul_comm _ _
    rw [hr,map_smul]
    rfl
  have hsection : ∀ᵐ y ∂haarAddCircle,
      Integrable (fun ω=>‖W (y,ω)‖^2) μ ∧ (∫ ω,‖W (y,ω)‖^2 ∂μ)≤C*e y^χ := by
    filter_upwards [Measure.ae_ae_of_ae_prod hMom] with y hy
    have hs := NativeRandomRows.correlated_input_negative μ
      (hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
      (fun ω=>D (ω,y)) (hD.comp (measurable_id.prodMk measurable_const)) (hD2 y)
      hB (fun ω x=>hb ω y x) hΛ hρ hρhalf ht ht1 hA (center y)
      hχ0 hχ1 hCD hCG p hp horder (hiDh y) (hbDh y) (hheat y) hy
    have he : (A*Real.sqrt ((∫ ω,D (ω,y)^2 ∂μ)^χ*((CD+CG)/2)^(1/(p:ℝ))))^2=
        A^2*(e y^χ*((CD+CG)/2)^(1/(p:ℝ))) := by
      rw [mul_pow,Real.sq_sqrt (mul_nonneg (rpow_nonneg (he0 y) _) (rpow_nonneg (by positivity) _))]
    refine ⟨by simpa only [hWe,Function.comp_apply] using hs.1,?_⟩
    have hh := hs.2.1
    rw [he] at hh
    simpa only [hWe,C,Function.comp_apply,mul_assoc,mul_left_comm,mul_comm] using hh
  let a : HeatCircle→ℝ := fun y=>Real.sqrt (C*e y^χ)
  have haEq (y : HeatCircle) : a y=Real.sqrt C*e y^(χ/2) :=
    CorrelatedLinearInput.sqrt_mul_power hC (he0 y)
  have hα : 0≤χ/2 := div_nonneg hχ0 (by norm_num)
  have hα1 : χ/2≤1 := by linarith
  have hpower := CorrelatedLinearInput.fractional_mass haarAddCircle e hem hiD2 he0 hα hα1
  have ham : Measurable a := (measurable_const.mul (hem.pow_const χ)).sqrt
  have hai : Integrable a haarAddCircle := by
    change Integrable (fun y=>a y) haarAddCircle
    simp_rw [haEq]
    exact hpower.1.const_mul (Real.sqrt C)
  have hmain := HilbertParameterAverage.finite_energy μ haarAddCircle W hW a ham hai
    (fun y=>Real.sqrt_nonneg _) (hsection.mono (fun y hy=>hy.1))
    (hsection.mono (fun y hy=>by
      rw [Real.sq_sqrt (mul_nonneg hC (rpow_nonneg (he0 y) χ))]
      exact hy.2))
  have hout (ω : Ω) : OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))=
      ∫ y,W (y,ω) ∂haarAddCircle := by
    rw [←ContinuousLinearMap.comp_apply,←negative_synthesis_eq hΛ hρ.le hF hB hb ω,
      KernelOperator.synthesis_eq_integral]
    apply integral_congr_ae
    filter_upwards [negativeKernel_ae hΛ hρ.le hF hB hb ω,hv ω] with y hy hvy
    rw [hy,hvy]
  refine ⟨by simpa only [hout] using hmain.2.1,?_⟩
  have hbMass : (∫ y,a y ∂haarAddCircle)≤Real.sqrt C*(∫ y,e y ∂haarAddCircle)^(χ/2) := by
    simp_rw [haEq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hpower.2 (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (integral_nonneg (fun y=>Real.sqrt_nonneg (C*e y^χ))) hbMass 2
  have hpow : ((∫ y,e y ∂haarAddCircle)^(χ/2))^2=(∫ y,e y ∂haarAddCircle)^χ := by
    rw [←Real.rpow_mul_natCast (integral_nonneg he0)]
    congr 1
    ring
  rw [mul_pow,Real.sq_sqrt hC,hpow] at hsq
  have hm : (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2 ∂μ)≤
      (∫ y,a y ∂haarAddCircle)^2 := by simpa only [hout] using hmain.2.2
  exact hm.trans hsq

end SHE.NativeRandomKernel
