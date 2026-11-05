module
public import SHE.NativeDampedInputEnergy
public import SHE.ContinuousHeatMild
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeBieleckiItoEnergy
open MeasureTheory Set PredictableL2 FiniteHaar LowBands
open scoped NNReal ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2 :=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance (ell M : ℝ) : MeasurableSpace (EllipticField ell M) := borel _
local instance (ell M : ℝ) : BorelSpace (EllipticField ell M) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) (hH : (H:ℝ) ≤ 1) {Λ ell M : ℝ}
variable (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ H)

/-- The actual terminal integral at every target, clamped only outside
its declared horizon so the expression is globally defined. -/
def value (f : ℝ≥0 × Ω → EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) (t : ℝ≥0) : Ω → StateL2 :=
  I.integral (NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM f hf (min t H)
    (min_le_right _ _) (le_trans (by exact_mod_cast min_le_right t H) hH))

theorem value_of_le (f : ℝ≥0 × Ω → EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) (t : ℝ≥0) (ht : t ≤ H) :
    value 𝓕 μ H hH hΛ hell hM I f hf t =
    I.integral (NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM f hf t ht
      (le_trans (by exact_mod_cast ht) hH)) := by
  unfold value
  simp only [min_eq_left ht]

/-- Exact weighted energy from the SAME native terminal integral.
This does not assume a native stochastic convolution map or its law. -/
theorem weighted
    (f g : ℝ≥0 × Ω → EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) (hg : StronglyMeasurable[𝓕.predictable] g)
    (γ : ℝ) :
    (∫⁻t, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ)) *
      ‖value 𝓕 μ H hH hΛ hell hM I f hf t ω -
        value 𝓕 μ H hH hΛ hell hM I g hg t ω‖^2) ∂μ ∂timeMeasure H) =
    ∫⁻t, ∫⁻s, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ)) *
      (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ))) *
      ‖NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω)) -
        NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),g (s,ω))‖^2))
      ∂μ ∂timeMeasure t ∂timeMeasure H := by
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem H] with t ht
  rw [value_of_le 𝓕 μ H hH hΛ hell hM I f hf t ht.2,
    value_of_le 𝓕 μ H hH hΛ hell hM I g hg t ht.2]
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [NativeDampedInputEnergy.fixed 𝓕 μ H hΛ hell hM f g hf hg I t ht.2
    (le_trans (by exact_mod_cast ht.2) hH)]
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The actual native stochastic coefficient difference contracts in
weighted energy. Only ordinary terminal Ito isometry is used. -/
theorem lipschitz
    {a : ℝ → ℝ} (ha : Measurable a) (hb : ∀z, ell ≤ a z ∧ a z ≤ M)
    (hcoef : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (U V : ℝ≥0 × Ω → StateL2)
    (hU : StronglyMeasurable[𝓕.predictable] U) (hV : StronglyMeasurable[𝓕.predictable] V)
    {γ : ℝ} (hγ : 0 < γ) :
    (∫⁻t, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ)) *
      ‖value 𝓕 μ H hH hΛ hell hM I
        (fun p => NonlinearHaarIntegrand.coefficientField a ha ell M hell hb (U p))
        (hcoef.comp hU.measurable).stronglyMeasurable t ω -
      value 𝓕 μ H hH hΛ hell hM I
        (fun p => NonlinearHaarIntegrand.coefficientField a ha ell M hell hb (V p))
        (hcoef.comp hV.measurable).stronglyMeasurable t ω‖^2) ∂μ ∂timeMeasure H) ≤
    ENNReal.ofReal (NativeBieleckiColumnEnergy.constant ell M L * BieleckiKernel.mass γ) *
      (∫⁻s, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ)) * ‖U (s,ω)-V (s,ω)‖^2)
        ∂μ ∂timeMeasure H) := by
  rw [weighted]
  exact NativeBieleckiColumnEnergy.expected_energy μ ha hell hb
    (NonlinearHaarIntegrand.absBound hell hb) hLip H hH U V
    ((hU.mono (predictable_le_product 𝓕)).measurable)
    ((hV.mono (predictable_le_product 𝓕)).measurable) hΛ hγ
end SHE.NativeBieleckiItoEnergy
