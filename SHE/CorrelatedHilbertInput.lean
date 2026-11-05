module

public import SHE.CorrelatedKernelInput
public import SHE.KernelActionFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance correlatedHilbertInput_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance correlatedHilbertInput_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance correlatedHilbertInput_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance correlatedHilbertInput_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance correlatedHilbertInput_nativeSecondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance correlatedHilbertInput_kernelSigma : MeasurableSpace KernelSpace := borel _
local instance correlatedHilbertInput_kernelBorel : BorelSpace KernelSpace := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A genuinely dependent Hilbert input is controlled through its
GLOBAL Hilbert moments. Pathwise Hilbert--Schmidt Cauchy is applied
before expectation, so no random input is substituted into a Gaussian
estimate for fixed directions and no pointwise L2 representative is used. -/
theorem correlated_hilbert_input_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω×(HeatCircle×HeatCircle)→ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0≤B) (hb : ∀ ω y x,‖F (ω,(y,x))‖≤B)
    (v : Ω→CircleL2) (hv : Measurable v) (hv2 : Integrable (fun ω=>‖v ω‖^2) μ)
    {Λ ρ t A χ CD CG : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hA : 0<A) (center : HeatCircle→HeatCircle)
    (hχ0 : 0≤χ) (hχ1 : χ<1) (hCD : 0≤CD) (hCG : 0≤CG)
    (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (hiV : Integrable (fun ω=>‖v ω‖^((4*(p:ℝ))*(1-χ))) μ)
    (hbV : (∫ ω,‖v ω‖^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD)
    (hheat : ∀ y x,0<‖ProfileVariance.heatPhysical (8*t) (center y) x‖)
    (hMom : ∀ᵐ z : HeatCircle×HeatCircle ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      Integrable (fun ω=>(‖F (ω,z)‖/(A*‖ProfileVariance.heatPhysical (8*t) (center z.1) z.2‖))^(4*p)) μ ∧
      (∫ ω,(‖F (ω,z)‖/(A*‖ProfileVariance.heatPhysical (8*t) (center z.1) z.2‖))^(4*p) ∂μ)≤CG) :
    let C := GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*A^2*((CD+CG)/2)^(1/(p:ℝ))
    Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2 ∂μ)≤
        C*(∫ ω,‖v ω‖^2 ∂μ)^χ := by
  intro C
  let N : Ω→ℝ := fun ω=>‖v ω‖
  have hN : Measurable N := hv.norm
  have hN2 : MemLp N 2 μ := (memLp_two_iff_integrable_sq hN.aestronglyMeasurable).mpr hv2
  let W : Ω×HeatCircle→CircleL2 := fun z=>(N z.1:ℂ) • negativeColumn Λ ρ hΛ hρ.le F z
  have hW : Measurable W := (Complex.continuous_ofReal.measurable.comp (hN.comp measurable_fst)).smul
    (negativeColumn_measurable hΛ hρ.le hF hb)
  have hWb (ω : Ω) (y : HeatCircle) : ‖W (ω,y)‖≤B*N ω := by
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (negativeColumn_norm_le hΛ hρ.le hF hB hb (ω,y)) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hWi : Integrable (fun z : Ω×HeatCircle=>‖W z‖^2) (μ.prod haarAddCircle) := by
    apply ((hv2.const_mul (B^2)).comp_fst haarAddCircle).mono' (hW.norm.pow_const 2).aestronglyMeasurable
    refine ae_of_all _ (fun z=>?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [N,mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hWb z.1 z.2) 2
  have hWe (y : HeatCircle) (ω : Ω) : W (ω,y)=OneInputOperator.besselHalf Λ ρ hΛ hρ.le
      (NativeRandomRows.nativeRow (fun z : Ω×HeatCircle=>F (z.1,(y,z.2))*(N z.1:ℂ)) ω) := by
    have hFy : Measurable (fun z : Ω×HeatCircle=>F (z.1,(y,z.2))) :=
      hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have hprod : Measurable (fun z : Ω×HeatCircle=>F (z.1,(y,z.2))*(N z.1:ℂ)) :=
      hFy.mul (Complex.continuous_ofReal.measurable.comp (hN.comp measurable_fst))
    have hbound (ω : Ω) (x : HeatCircle) : ‖F (ω,(y,x))*(N ω:ℂ)‖≤B*N ω := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hb ω y x) (norm_nonneg _)
    have hr : NativeRandomRows.nativeRow
        (fun z : Ω×HeatCircle=>F (z.1,(y,z.2))*(N z.1:ℂ)) ω=(N ω:ℂ) • column F (ω,y) := by
      apply Lp.ext
      filter_upwards [NativeRandomRows.nativeRow_ae_cap hprod (fun ω=>B*N ω) hbound ω,
        column_ae hF hb ω y,Lp.coeFn_smul (N ω:ℂ) (column F (ω,y))] with x hx hy hz
      rw [hx,hz,Pi.smul_apply,smul_eq_mul,hy]
      exact mul_comm _ _
    rw [hr,map_smul]
    rfl
  have hsec : ∀ᵐ y ∂haarAddCircle,(∫ ω,‖W (ω,y)‖^2 ∂μ)≤C*(∫ ω,‖v ω‖^2 ∂μ)^χ := by
    filter_upwards [Measure.ae_ae_of_ae_prod hMom] with y hy
    have hs := NativeRandomRows.correlated_input_negative μ
      (hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))) N hN hN2
      hB (fun ω x=>hb ω y x) hΛ hρ hρhalf ht ht1 hA (center y) hχ0 hχ1 hCD hCG p hp horder
      (by simpa only [N,abs_of_nonneg (norm_nonneg _)] using hiV)
      (by simpa only [N,abs_of_nonneg (norm_nonneg _)] using hbV) (hheat y) hy
    have hh := hs.2.1
    have hpw : (A*sqrt ((∫ ω,N ω^2 ∂μ)^χ*((CD+CG)/2)^(1/(p:ℝ))))^2=
        A^2*((∫ ω,N ω^2 ∂μ)^χ*((CD+CG)/2)^(1/(p:ℝ))) := by
      rw [mul_pow,sq_sqrt (mul_nonneg (rpow_nonneg (integral_nonneg (fun _=>sq_nonneg _)) _) (rpow_nonneg (by positivity) _))]
    rw [hpw] at hh
    simpa only [hWe,C,N,Function.comp_apply,mul_assoc,mul_left_comm,mul_comm] using hh
  have hHs : (fun ω=>‖(N ω:ℂ) • negativeKernel Λ ρ hΛ hρ.le F ω‖^2)=
      (fun ω=>∫ y,‖W (ω,y)‖^2 ∂haarAddCircle) := by
    funext ω
    rw [StoppedFourier.L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul (N ω:ℂ) (negativeKernel Λ ρ hΛ hρ.le F ω),
      negativeKernel_ae hΛ hρ.le hF hB hb ω] with y hy hz
    rw [hy,Pi.smul_apply,hz]
  have hHi : Integrable (fun ω=>‖(N ω:ℂ) • negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ := by
    rw [hHs]
    exact hWi.integral_prod_left
  have hHb : (∫ ω,‖(N ω:ℂ) • negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ)≤C*(∫ ω,‖v ω‖^2 ∂μ)^χ := by
    rw [hHs,integral_integral_swap hWi]
    exact (integral_mono_ae hWi.integral_prod_right (integrable_const _) hsec).trans_eq (by simp)
  have hpoint (ω : Ω) : ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2≤
      ‖(N ω:ℂ) • negativeKernel Λ ρ hΛ hρ.le F ω‖^2 := by
    have hh := ((KernelOperator.synthesis (negativeKernel Λ ρ hΛ hρ.le F ω)).le_opNorm (v ω)).trans
      (mul_le_mul_of_nonneg_right (KernelOperator.synthesis_norm_le _) (norm_nonneg _))
    rw [negative_synthesis_eq hΛ hρ.le hF hB hb ω,ContinuousLinearMap.comp_apply] at hh
    have hn : ‖(N ω:ℂ) • negativeKernel Λ ρ hΛ hρ.le F ω‖=
        ‖negativeKernel Λ ρ hΛ hρ.le F ω‖*‖v ω‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),mul_comm]
    rw [hn]
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hout := (OneInputOperator.besselHalf Λ ρ hΛ hρ.le).continuous.measurable.comp
    (action_measurable hF (fun ω=>⟨B,hb ω⟩) v hv)
  have hoi : Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2) μ := by
    apply hHi.mono' (hout.norm.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by rw [Real.norm_of_nonneg (sq_nonneg _)];exact hpoint ω)
  exact ⟨hoi,(integral_mono hoi hHi hpoint).trans hHb⟩

end SHE.NativeRandomKernel
