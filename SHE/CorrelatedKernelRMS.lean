module

public import SHE.CorrelatedLinearInput
public import SHE.NativeRandomCap

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.CorrelatedLinearInput
open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The normalized kernel and the input may share every noise variable.
Their actual higher moments supply the RMS estimate; only the genuine
second moment of the input carries the smallness factor. -/
theorem normalized_rms [IsProbabilityMeasure μ]
    (D : Ω→ℝ) (F : Ω→ℂ) (hD : MemLp D 2 μ) (hF : AEStronglyMeasurable F μ)
    {s χ CD CG : ℝ} (hs : 0<s) (hχ0 : 0≤χ) (hχ1 : χ<1)
    (hCD : 0≤CD) (hCG : 0≤CG) (p : ℕ) (hp : 0<p)
    (horder : 1≤(p:ℝ)*(1-χ))
    (hiD : Integrable (fun ω=>|D ω|^((4*(p:ℝ))*(1-χ))) μ)
    (hiF : Integrable (fun ω=>(‖F ω‖/s)^(4*p)) μ)
    (hbD : (∫ ω,|D ω|^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD)
    (hbF : (∫ ω,(‖F ω‖/s)^(4*p) ∂μ)≤CG) :
    Integrable (fun ω=>‖F ω*(D ω:ℂ)‖^2) μ ∧
      Real.sqrt (∫ ω,‖F ω*(D ω:ℂ)‖^2 ∂μ)≤
        s*Real.sqrt ((∫ ω,D ω^2 ∂μ)^χ*((CD+CG)/2)^(1/(p:ℝ))) := by
  let G : Ω→ℝ := fun ω=>‖F ω‖/s
  have hG : AEStronglyMeasurable G μ := (hF.norm.aemeasurable.div_const s).aestronglyMeasurable
  have hG0 (ω : Ω) : 0≤G ω := div_nonneg (norm_nonneg _) hs.le
  have hh := energy D G hD hG hχ0 hχ1 hCD hCG p hp horder hiD
    (by simpa only [abs_of_nonneg (hG0 _)] using hiF) hbD
    (by simpa only [abs_of_nonneg (hG0 _)] using hbF)
  have he (ω : Ω) : ‖F ω*(D ω:ℂ)‖^2=s^2*(D ω*G ω)^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    dsimp only [G]
    field_simp
    <;> ring
  have hi : Integrable (fun ω=>‖F ω*(D ω:ℂ)‖^2) μ := by
    simpa only [he] using hh.1.integrable_sq.const_mul (s^2)
  refine ⟨hi,?_⟩
  have hb : (∫ ω,‖F ω*(D ω:ℂ)‖^2 ∂μ)≤
      s^2*((∫ ω,D ω^2 ∂μ)^χ*((CD+CG)/2)^(1/(p:ℝ))) := by
    simp_rw [he]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hh.2 (sq_nonneg _)
  have h := Real.sqrt_le_sqrt hb
  rwa [Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq hs.le] at h

end SHE.CorrelatedLinearInput

namespace SHE.NativeRandomRows
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
open scoped ENNReal
local instance correlatedKernelRMS_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance correlatedKernelRMS_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance correlatedKernelRMS_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance correlatedKernelRMS_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Actual correlated kernel-input row, with native Bessel output.
This is a linear input theorem, not a substitution of a random direction
into a Gaussian estimate for fixed directions. -/
theorem correlated_input_negative (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω×HeatCircle→ℂ} (hF : Measurable F) (D : Ω→ℝ) (hDm : Measurable D)
    (hD : MemLp D 2 μ) {B : ℝ} (hB : 0≤B) (hb : ∀ ω x,‖F (ω,x)‖≤B)
    {Λ ρ t A χ CD CG : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hA : 0<A) (a : HeatCircle)
    (hχ0 : 0≤χ) (hχ1 : χ<1) (hCD : 0≤CD) (hCG : 0≤CG)
    (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (hiD : Integrable (fun ω=>|D ω|^((4*(p:ℝ))*(1-χ))) μ)
    (hbD : (∫ ω,|D ω|^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD)
    (hheat : ∀ x,0<‖ProfileVariance.heatPhysical (8*t) a x‖)
    (hMom : ∀ᵐ x ∂haarAddCircle,
      Integrable (fun ω=>(‖F (ω,x)‖/(A*‖ProfileVariance.heatPhysical (8*t) a x‖))^(4*p)) μ ∧
      (∫ ω,(‖F (ω,x)‖/(A*‖ProfileVariance.heatPhysical (8*t) a x‖))^(4*p) ∂μ)≤CG) :
    let G := fun z : Ω×HeatCircle=>F z*(D z.1:ℂ)
    let I := Real.sqrt ((∫ ω,D ω^2 ∂μ)^χ*((CD+CG)/2)^(1/(p:ℝ)))
    Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow G ω)‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow G ω)‖^2 ∂μ)≤
        GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*(A*I)^2 ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow G ω)‖^2 ∂μ)≤
        GaussianNegativePacket.traceConstant*Λ^(-ρ)*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*(A*I)^2 := by
  intro G I
  have hG : Measurable G := hF.mul (Complex.continuous_ofReal.measurable.comp (hDm.comp measurable_fst))
  let cap : Ω→ℝ := fun ω=>B*|D ω|
  have hcap : Measurable cap := measurable_const.mul hDm.norm
  have hci : Integrable (fun ω=>cap ω^2) μ := by
    simpa only [cap,mul_pow,sq_abs] using hD.integrable_sq.const_mul (B^2)
  have hGb (ω : Ω) (x : HeatCircle) : ‖G (ω,x)‖≤cap ω := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb ω x) (abs_nonneg _)
  have hsharp : ∀ᵐ x ∂haarAddCircle,rms μ G x≤(A*I)*‖ProfileVariance.heatPhysical (8*t) a x‖ := by
    filter_upwards [hMom] with x hx
    have hh := CorrelatedLinearInput.normalized_rms D (fun ω=>F (ω,x)) hD
      ((hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (mul_pos hA (hheat x)) hχ0 hχ1 hCD hCG p hp horder hiD hx.1 hbD hx.2
    change Real.sqrt (∫ ω,‖F (ω,x)*(D ω:ℂ)‖^2 ∂μ)≤_
    convert! hh.2 using 1 <;> ring
  exact expected_dominated_negative_cap_ae μ hG cap hcap hci hGb hΛ hρ hρhalf ht ht1
    (mul_nonneg hA.le (Real.sqrt_nonneg _)) a hsharp

end SHE.NativeRandomRows
