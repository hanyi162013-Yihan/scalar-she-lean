module

public import SHE.TimeDilationEquivalence
public import SHE.HaarFieldScaling
public import SHE.DampedFixedIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ClockedHaarIntegral
open MeasureTheory Set Filter PredictableL2 FiniteHaar PredictableTimeDilation
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable {Λ ell M : ℝ} (hΛ : 0≤Λ) (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M)
variable (hf : StronglyMeasurable[(filtration 𝓕 (clock c hc)).predictable] f)

def unitField (p : ℝ≥0×Ω) : EllipticField ((c:ℝ)*ell) ((c:ℝ)*M) :=
  HaarFieldScaling.scale (c:ℝ) hc (f (clock c hc p.1,p.2))

include hf in
theorem unitField_predictable : StronglyMeasurable[𝓕.predictable] (unitField c hc f) := by
  have hg := hf.comp_measurable (measurable_forward 𝓕 (clock c hc))
  exact (HaarFieldScaling.continuous_scale (c:ℝ) hc).comp_stronglyMeasurable hg

def unitTime (t : ℝ≥0) : ℝ≥0 := min h ((clock c hc).symm t)

theorem unitTime_eq {t : ℝ≥0} (ht : t≤c*h) : unitTime c hc h t=(clock c hc).symm t := by
  apply min_eq_right
  change c⁻¹*t≤h
  have hh' := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr c.2)
  simpa only [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using hh'

def unitInput (t : ℝ≥0) : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h :=
  DampedFixedIntegral.input 𝓕 μ h hh (mul_nonneg c.2 hΛ) (mul_pos hc hell) (mul_nonneg c.2 hM)
    (unitField c hc f) (unitField_predictable 𝓕 c hc f hf) (unitTime c hc h t) (min_le_left _ _)

/-- A constructed physical-clock input, obtained from the actual unit
fixed-terminal heat integral by the complete predictable equivalence. -/
def input (t : ℝ≥0) : Process (E := RealHaarIntegrand.Columns) (filtration 𝓕 (clock c hc)) μ (c*h) :=
  (processEquivalence 𝓕 μ c hc h).symm (unitInput 𝓕 μ c hc h hh hΛ hell hM f hf t)

def kernel (t : ℝ≥0) (p : ℝ≥0×Ω) : RealHaarIntegrand.Columns :=
  Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) • RealHaarIntegrand.kernel ell M hell
    (((t:ℝ)-(p.1:ℝ))/(c:ℝ),f p)

theorem scaled_kernel {t s : ℝ≥0} (g : EllipticField ell M) :
    Real.sqrt (c:ℝ)⁻¹ • DampedHeatKernel.kernel ((c:ℝ)*Λ) ((c:ℝ)*ell) ((c:ℝ)*M)
      (mul_pos hc hell) (((((clock c hc).symm t:ℝ≥0):ℝ)-(((clock c hc).symm s:ℝ≥0):ℝ)),
        HaarFieldScaling.scale (c:ℝ) hc g)=
      Real.exp (-Λ*((t:ℝ)-(s:ℝ))) • RealHaarIntegrand.kernel ell M hell
        (((t:ℝ)-(s:ℝ))/(c:ℝ),g) := by
  have hage : ((((clock c hc).symm t:ℝ≥0):ℝ)-(((clock c hc).symm s:ℝ≥0):ℝ))=
      ((t:ℝ)-(s:ℝ))/(c:ℝ) := by
    change (c:ℝ)⁻¹*(t:ℝ)-(c:ℝ)⁻¹*(s:ℝ)=_
    ring
  rw [hage,DampedHeatKernel.kernel,HaarFieldScaling.real_kernel_scale hell (c:ℝ) hc]
  have hexp : -((c:ℝ)*Λ)*(((t:ℝ)-(s:ℝ))/(c:ℝ))=-Λ*((t:ℝ)-(s:ℝ)) := by
    field_simp [show (c:ℝ)≠0 from (show 0<(c:ℝ) from hc).ne']
  rw [hexp,smul_smul,smul_smul]
  have hs := ScaledLpPull.sqrt_mul_sqrt_inv (c:ℝ) hc
  have hs' : Real.sqrt (c:ℝ)⁻¹*Real.sqrt (c:ℝ)=1 := by simpa only [mul_comm] using hs
  have hscalar : Real.sqrt (c:ℝ)⁻¹*(Real.exp (-Λ*((t:ℝ)-(s:ℝ)))*Real.sqrt (c:ℝ))=
      Real.exp (-Λ*((t:ℝ)-(s:ℝ))) := by
    calc
      _=Real.exp (-Λ*((t:ℝ)-(s:ℝ)))*(Real.sqrt (c:ℝ)⁻¹*Real.sqrt (c:ℝ)) := by ring
      _=_ := by rw [hs',mul_one]
  simpa only [mul_assoc] using congrArg
    (fun r : ℝ => r•RealHaarIntegrand.kernel ell M hell (((t:ℝ)-(s:ℝ))/(c:ℝ),g)) hscalar

/-- Identification with the literal native-clock heat-Haar integrand.
No native convolution map or mild-equation input is supplied. -/
theorem input_ae (t : ℝ≥0) (ht : t≤c*h) :
    input 𝓕 μ c hc h hh hΛ hell hM f hf t=ᵐ[energyMeasure μ (c*h)] kernel (Λ := Λ) c hell f t := by
  have hunit := DampedFixedIntegral.input_ae 𝓕 μ h hh (mul_nonneg c.2 hΛ) (mul_pos hc hell)
    (mul_nonneg c.2 hM) (unitField c hc f) (unitField_predictable 𝓕 c hc f hf)
    (unitTime c hc h t) (min_le_left _ _)
  have hrev := ScaledLpPull.inverse_preserving (energyMeasure μ h) (energyMeasure μ (c*h))
    (c:ℝ) hc (ambientEquiv c hc) (energyMeasure_clock_preserving c hc h μ)
  have hu := hrev.quasiMeasurePreserving.ae hunit
  have hu' := (Measure.ae_ennreal_smul_measure_iff
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (show (0:ℝ)<c from hc)))).mp hu
  filter_upwards [processEquivalence_symm_ae 𝓕 μ c hc h (unitInput 𝓕 μ c hc h hh hΛ hell hM f hf t),hu']
    with p hp hq
  change unitInput 𝓕 μ c hc h hh hΛ hell hM f hf t ((clock c hc).symm p.1,p.2)=
    DampedFixedIntegral.kernel (Λ := (c:ℝ)*Λ) (mul_pos hc hell) (unitField c hc f)
      (unitTime c hc h t) ((clock c hc).symm p.1,p.2) at hq
  rw [input,hp,hq]
  simp only [DampedFixedIntegral.kernel,unitField]
  rw [unitTime_eq c hc h ht,OrderIso.apply_symm_apply]
  exact scaled_kernel c hc hell (t := t) (s := p.1) (f p)

theorem integral_input (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (t : ℝ≥0) :
    (PredictableTimeDilation.integral 𝓕 μ c hc h I).integral (input 𝓕 μ c hc h hh hΛ hell hM f hf t)=
      I.integral (unitInput 𝓕 μ c hc h hh hΛ hell hM f hf t) :=
  PredictableTimeDilation.integral_push 𝓕 μ c hc h I _

end SHE.ClockedHaarIntegral
