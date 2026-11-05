module
public import SHE.NativeBieleckiItoEnergy
public import SHE.NativeWeightedProcess
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeStoppedNoiseIncrement
open MeasureTheory PredictableL2 FiniteHaar LowBands
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
variable (I : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
variable {a : ℝ → ℝ} (ha : Measurable a) (hb : ∀z, ell ≤ a z ∧ a z ≤ M)
variable (hcoef : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
variable (W : ℝ≥0 × Ω → StateL2) (hW : StronglyMeasurable[𝓕.predictable] W)
variable (d : Process (E:=StateL2) 𝓕 μ H)

def noise (t : ℝ≥0) (ω : Ω) : StateL2 :=
  NativeBieleckiItoEnergy.value 𝓕 μ H hH hΛ hell hM I
    (fun p => NonlinearHaarIntegrand.coefficientField a ha ell M hell hb (W p+d p))
    (hcoef.comp (hW.add (Lp.stronglyMeasurable d)).measurable).stronglyMeasurable t ω -
  NativeBieleckiItoEnergy.value 𝓕 μ H hH hΛ hell hM I
    (fun p => NonlinearHaarIntegrand.coefficientField a ha ell M hell hb (W p))
    (hcoef.comp hW.measurable).stronglyMeasurable t ω

/-- The actual smooth stochastic increment depends quantitatively only
on the stopped L2 difference, irrespective of the size of the base path. -/
theorem energy {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    {γ : ℝ} (hγ : 0 < γ) :
    (∫⁻t, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ)) *
      ‖noise 𝓕 μ H hH hΛ hell hM I ha hb hcoef W hW d t ω‖^2) ∂μ ∂timeMeasure H) ≤
    ENNReal.ofReal (NativeBieleckiColumnEnergy.constant ell M L * BieleckiKernel.mass γ) *
      NativeWeightedProcess.energy 𝓕 μ H γ d := by
  have he := NativeBieleckiItoEnergy.lipschitz 𝓕 μ H hH hΛ hell hM I ha hb hcoef hLip
    (fun p => W p+d p) W (hW.add (Lp.stronglyMeasurable d)) hW hγ
  simpa only [noise, NativeWeightedProcess.energy, add_sub_cancel_left] using he
end SHE.NativeStoppedNoiseIncrement
