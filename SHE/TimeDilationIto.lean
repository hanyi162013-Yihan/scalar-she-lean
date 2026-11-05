module

public import SHE.TimeDilationLp
public import SHE.StandardTerminalConditionalBDG

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory Set Filter PredictableL2
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

/-- The same terminal integral in the rescaled physical clock. The
input pull has its exact square-root Jacobian, and stopped adaptedness
uses the inverse deterministic clock. -/
def integral (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) :
    StandardTerminalIto (C := C) (E := E) (filtration 𝓕 (clock c hc)) μ (c*h) where
  integral := I.integral.comp (processIsometry 𝓕 μ c hc h)
  adapted l v hv := I.adapted ((clock c hc).symm l) _ (processIsometry_stopped 𝓕 μ c hc h l v hv)
  centered v := I.centered _

def timeEquiv : ℝ≥0≃ᵐℝ≥0 where
  toEquiv := (clock c hc).toEquiv
  measurable_toFun := (clock_continuous c hc).measurable
  measurable_invFun := (clock_symm_continuous c hc).measurable

/-- Equality of the actual samplewise quadratic energies, with no
conditional expectation or stochastic estimate used in its proof. -/
theorem bracket_ae (v : Process (E := C) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    ∀ᵐ ω ∂μ,(∫⁻ s,ENNReal.ofReal (‖processIsometry 𝓕 μ c hc h v (s,ω)‖^2) ∂timeMeasure h)=
      ∫⁻ t,ENNReal.ofReal (‖v (t,ω)‖^2) ∂timeMeasure (c*h) := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae
    (processIsometry_ae 𝓕 μ c hc h v)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  calc
    _=∫⁻ s,ENNReal.ofReal ((c:ℝ)*‖v (clock c hc s,ω)‖^2) ∂timeMeasure h := by
      apply lintegral_congr_ae
      filter_upwards [hω] with s hs
      dsimp only [Prod.swap] at hs
      rw [hs,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow]
      exact congrArg (fun a : ℝ => ENNReal.ofReal (a*‖v (clock c hc s,ω)‖^2)) (Real.sq_sqrt c.2)
    _=∫⁻ s,ENNReal.ofReal (c:ℝ)*ENNReal.ofReal (‖v (clock c hc s,ω)‖^2) ∂timeMeasure h := by
      apply lintegral_congr
      intro s
      exact ENNReal.ofReal_mul c.2
    _=∫⁻ s,ENNReal.ofReal (‖v (clock c hc s,ω)‖^2) ∂(ENNReal.ofReal (c:ℝ) • timeMeasure h) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_smul_measure]
      rfl
    _=_ := (timeMeasure_clock_preserving c hc h).lintegral_comp_emb (timeEquiv c hc).measurableEmbedding
      (fun t => ENNReal.ofReal (‖v (t,ω)‖^2))

theorem bdgPower (p : ℕ) (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p I B) :
    StandardTerminalBDGPower p (integral 𝓕 μ c hc h I) B := by
  intro v
  apply (hBDG (processIsometry 𝓕 μ c hc h v)).trans_eq
  congr 1
  apply lintegral_congr_ae
  filter_upwards [bracket_ae 𝓕 μ c hc h v] with ω hω
  rw [hω]

theorem bdg16 (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) :
    StandardTerminalBDG16 (integral 𝓕 μ c hc h I) B := bdgPower 𝓕 μ c hc h 8 I B hBDG

theorem conditionalBdgPower (p : ℕ) (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalConditionalBDGPower p I B) :
    StandardTerminalConditionalBDGPower p (integral 𝓕 μ c hc h I) B := by
  intro A hA v
  have h0 : filtration 𝓕 (clock c hc) 0=𝓕 0 := by
    change 𝓕 ((clock c hc).symm 0)=𝓕 0
    have he0 : (clock c hc).symm (0 : ℝ≥0)=0 := (clock c hc).symm.map_bot
    rw [he0]
  have hA' : MeasurableSet[𝓕 0] A := h0 ▸ hA
  apply (hBDG A hA' (processIsometry 𝓕 μ c hc h v)).trans_eq
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (bracket_ae 𝓕 μ c hc h v)] with ω hω
  rw [hω]

end SHE.PredictableTimeDilation
