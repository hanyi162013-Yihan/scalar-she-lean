module

public import SHE.DampedPredictableVersion
public import SHE.HeatInitialProcess

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.MildFirstL2Realization
open MeasureTheory Set PredictableL2 LowBands FiniteHaar
open scoped NNReal ENNReal
local instance mildFirstL2Realization_finite : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance mildFirstL2Realization_stateSigma : MeasurableSpace StateL2:=borel _
local instance mildFirstL2Realization_stateBorel : BorelSpace StateL2:=⟨rfl⟩
local instance mildFirstL2Realization_nativeSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mildFirstL2Realization_nativeBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance mildFirstL2Realization_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance mildFirstL2Realization_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable {ell₀ M₀ ell₁ M₁ : ℝ} (hell₀ : 0<ell₀) (hM₀ : 0≤M₀) (hell₁ : 0<ell₁) (hM₁ : 0≤M₁)
variable (f₀ : ℝ≥0×Ω→EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (f₁ : ℝ≥0×Ω→EllipticField ell₁ M₁) (hf₁ : StronglyMeasurable[𝓕.predictable] f₁)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ h)

/-- Finite predictable L² energy of a given two-noise mild first path is
a CONCLUSION of its literal mild equation and the constructed actual
heat convolutions. No prior solution energy or coefficient Lipschitz
condition is assumed. Ordinary BDG16 is used only for jointly measurable
fixed-time versions of the same two stochastic integrals. -/
theorem exists_process (hpos : 0<h) (B₀ B₁ : ℝ≥0)
    (hBDG₀ : StandardTerminalBDG16 I₀ B₀) (hBDG₁ : StandardTerminalBDG16 I₁ B₁)
    (u₀ : StateL2) (U : ℝ≥0→Ω→StateL2)
    (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U))
    (hmild : ∀ t : ℝ≥0,∀ ht : t≤h,U t=ᵐ[μ] fun ω=>RealHeat.realHeat (t:ℝ) u₀+
      DampedFixedIntegral.value 𝓕 μ h hh (Λ:=0) (by norm_num) hell₀ hM₀ f₀ hf₀ I₀ t ht ω+
      DampedFixedIntegral.value 𝓕 μ h hh (Λ:=0) (by norm_num) hell₁ hM₁ f₁ hf₁ I₁ t ht ω) :
    ∃ V : Process (E:=StateL2) 𝓕 μ h,V=ᵐ[energyMeasure μ h] Function.uncurry U := by
  let N₀:=DampedStochasticConvolution.convolution 𝓕 μ h hh (Λ:=0) (by norm_num) hell₀ hM₀ I₀ f₀ hf₀
  let N₁:=DampedStochasticConvolution.convolution 𝓕 μ h hh (Λ:=0) (by norm_num) hell₁ hM₁ I₁ f₁ hf₁
  let Z₀:=DampedContinuousVersion.version 𝓕 μ h hh (Λ:=0) (by norm_num) hell₀ hM₀ f₀ hf₀ I₀
  let Z₁:=DampedContinuousVersion.version 𝓕 μ h hh (Λ:=0) (by norm_num) hell₁ hM₁ f₁ hf₁ I₁
  let V:=HeatInitialProcess.process 𝓕 μ h u₀+N₀+N₁
  let Z : ℝ≥0×Ω→StateL2:=fun p=>RealHeat.realHeat (p.1:ℝ) u₀+Z₀ p.1 p.2+Z₁ p.1 p.2
  have hZ₀:=DampedContinuousVersion.version_joint_measurable 𝓕 μ h hh (Λ:=0) (by norm_num)
    hell₀ hM₀ f₀ hf₀ I₀ B₀ hBDG₀ hpos
  have hZ₁:=DampedContinuousVersion.version_joint_measurable 𝓕 μ h hh (Λ:=0) (by norm_num)
    hell₁ hM₁ f₁ hf₁ I₁ B₁ hBDG₁ hpos
  have hZm : Measurable Z:=((HeatInitialProcess.predictable 𝓕 u₀).mono
    (predictable_le_product 𝓕)).measurable.add hZ₀ |>.add hZ₁
  have hUa : StronglyMeasurable (Function.uncurry U):=hU.mono (predictable_le_product 𝓕)
  have hUZ : Function.uncurry U=ᵐ[energyMeasure μ h] Z := by
    apply Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hUa.measurable hZm) |>.mpr
    filter_upwards [timeMeasure_ae_mem h] with t ht
    filter_upwards [hmild t ht.2,
      DampedContinuousVersion.version_ae_of_le 𝓕 μ h hh (Λ:=0) (by norm_num)
        hell₀ hM₀ f₀ hf₀ I₀ B₀ hBDG₀ hpos t ht.2,
      DampedContinuousVersion.version_ae_of_le 𝓕 μ h hh (Λ:=0) (by norm_num)
        hell₁ hM₁ f₁ hf₁ I₁ B₁ hBDG₁ hpos t ht.2] with ω hω h0 h1
    exact hω.trans (congrArg₂ (fun a b:StateL2=>a+b)
      (congrArg₂ (fun a b:StateL2=>a+b) rfl h0.symm) h1.symm)
  have hVZ : V=ᵐ[energyMeasure μ h] Z := by
    filter_upwards [HeatInitialProcess.process_ae 𝓕 μ h u₀,
      DampedPredictableVersion.convolution_ae_version 𝓕 μ h hh (Λ:=0) (by norm_num)
        hell₀ hM₀ f₀ hf₀ I₀ B₀ hBDG₀ hpos,
      DampedPredictableVersion.convolution_ae_version 𝓕 μ h hh (Λ:=0) (by norm_num)
        hell₁ hM₁ f₁ hf₁ I₁ B₁ hBDG₁ hpos,
      ae_eq_of_ae_eq_trim (Lp.coeFn_add (HeatInitialProcess.process 𝓕 μ h u₀) N₀),
      ae_eq_of_ae_eq_trim (Lp.coeFn_add (HeatInitialProcess.process 𝓕 μ h u₀+N₀) N₁)]
      with p hp h0 h1 ha hb
    change (HeatInitialProcess.process 𝓕 μ h u₀+N₀+N₁) p=Z p
    rw [hb]
    change (HeatInitialProcess.process 𝓕 μ h u₀+N₀) p+N₁ p=Z p
    rw [ha]
    change HeatInitialProcess.process 𝓕 μ h u₀ p+N₀ p+N₁ p=Z p
    rw [hp,h0,h1]
    rfl
  exact ⟨V,hVZ.trans hUZ.symm⟩

end SHE.MildFirstL2Realization
