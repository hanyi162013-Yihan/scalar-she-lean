module

public import SHE.TimeDilationInverseIto
public import SHE.ClockedPairIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ClockedPairIntegral
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar
open scoped NNReal ENNReal
local instance clockedOriginalIntegral_finite : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance clockedOriginalIntegral_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance clockedOriginalIntegral_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance clockedOriginalIntegral_nativeSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance clockedOriginalIntegral_nativeBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable {Λ ell M : ℝ} (hΛ : 0≤Λ) (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M)
variable (hf : StronglyMeasurable[(filtration 𝓕 (clock c hc)).predictable] f)

include hf in
/-- An arbitrary original native-clock integral of its literal kernel
is the pulled unit-clock fixed-terminal integral. This proves exact
same-noise realization, rather than constructing an unrelated native
integrator with the same covariance. -/
theorem original_terminal_eq
    (g : ℝ≥0×Ω→EllipticField ((c:ℝ)*ell) ((c:ℝ)*M))
    (hg : StronglyMeasurable[𝓕.predictable] g)
    (hfg : ClockedHaarIntegral.unitField c hc f=g)
    (J : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2)
      (filtration 𝓕 (clock c hc)) μ (c*h))
    (t : ℝ≥0) (ht : t≤h)
    (V : Process (E:=RealHaarIntegrand.Columns) (filtration 𝓕 (clock c hc)) μ (c*h))
    (hV : V=ᵐ[energyMeasure μ (c*h)] ClockedHaarIntegral.kernel (Λ:=Λ) c hell f (clock c hc t)) :
    J.integral V=DampedFixedIntegral.value 𝓕 μ h hh (mul_nonneg c.2 hΛ)
      (mul_pos hc hell) (mul_nonneg c.2 hM) g hg (inverseIntegral 𝓕 μ c hc h J) t ht := by
  have ht' : clock c hc t≤c*h:=mul_le_mul_of_nonneg_left ht c.2
  have he : V=ClockedHaarIntegral.input 𝓕 μ c hc h hh hΛ hell hM f hf (clock c hc t) := by
    apply Lp.ext
    apply ae_eq_trim_of_measurable (predictable_le_product (filtration 𝓕 (clock c hc)))
      (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
    exact hV.trans (ClockedHaarIntegral.input_ae 𝓕 μ c hc h hh hΛ hell hM f hf _ ht').symm
  have hh':=terminal_eq 𝓕 μ c hc h hh hΛ hell hM f hf g hg hfg
    (inverseIntegral 𝓕 μ c hc h J) (clock c hc t) ht'
  simp only [integral_inverseIntegral,OrderIso.symm_apply_apply] at hh'
  rw [he]
  exact hh'

end SHE.ClockedPairIntegral
