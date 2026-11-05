module

public import SHE.NativePairMild
public import SHE.NativePairKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativeAdditiveResidualPair
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A native-clock continuous pair with literal additive and residual
Haar kernels. The two mild equations are conclusions of the construction. -/
structure Solution (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
    (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ}
    (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
    (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (u₀ v₀ : StateL2) where
  first : ℝ≥0 → Ω → StateL2
  second : ℝ≥0 → Ω → StateL2
  first_continuous : ∀ ω,Continuous (fun t => first t ω)
  second_continuous : ∀ ω,Continuous (fun t => second t ω)
  first_predictable : StronglyMeasurable[𝓕.predictable] (Function.uncurry first)
  second_predictable : StronglyMeasurable[𝓕.predictable] (Function.uncurry second)
  first_coefficient : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb first)
  second_coefficient : StronglyMeasurable[𝓕.predictable] (coefficientFunction ha hell hb second)
  additiveInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  residualInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  controlledAdditiveInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  controlledResidualInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  additive_kernel : ∀ t,t≤h → additiveInput t=ᵐ[energyMeasure μ h]
    fun p => NativeHeatObservation.kernel κ κ hκ ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ)
  residual_kernel : ∀ t,t≤h → residualInput t=ᵐ[energyMeasure μ h]
    fun p => NativeHeatObservation.kernel ell M hell ((t:ℝ)-(p.1:ℝ),coefficientFunction ha hell hb first p)
  controlled_additive_kernel : ∀ t,t≤h → controlledAdditiveInput t=ᵐ[energyMeasure μ h]
    fun p => Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) •
      NativeHeatObservation.kernel κ κ hκ ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ)
  controlled_residual_kernel : ∀ t,t≤h → controlledResidualInput t=ᵐ[energyMeasure μ h]
    fun p => Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) •
      NativeHeatObservation.kernel ell M hell ((t:ℝ)-(p.1:ℝ),coefficientFunction ha hell hb second p)
  first_mild : ∀ t,t≤h → first t=ᵐ[μ]
    fun ω => NativeHeatObservation.heat (t:ℝ) u₀+I₀.integral (additiveInput t) ω+I₁.integral (residualInput t) ω
  second_mild : ∀ t,t≤h → second t=ᵐ[μ]
    fun ω => Real.exp (-Λ*(t:ℝ)) • NativeHeatObservation.heat (t:ℝ) v₀+
      Λ • NativeClock.volterra Λ (fun s => first s ω) t+
      I₀.integral (controlledAdditiveInput t) ω+I₁.integral (controlledResidualInput t) ω

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1) {Λ : ℝ} (hΛ : 0≤Λ)
variable (κ : ℝ) (hκ : 0<κ) {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (hm : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
variable (u₀ v₀ : StateL2)

def of_unit (S : AdditiveResidualPair.Solution 𝓕 μ h hh (mul_nonneg NativeClock.rate.2 hΛ)
    ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ)
    (ha.const_mul (NativeClock.rate:ℝ)) (mul_pos NativeClock.rate_pos hell)
    (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hb) I₀ I₁ u₀ v₀) :
    Solution (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
      Λ κ hκ ha hell hb
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀)
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁) u₀ v₀ where
  first := NativePairClock.path S.first
  second := NativePairClock.path S.second
  first_continuous := NativePairClock.path_continuous S.first S.first_continuous
  second_continuous := NativePairClock.path_continuous S.second S.second_continuous
  first_predictable := NativePairClock.path_predictable 𝓕 S.first S.first_predictable
  second_predictable := NativePairClock.path_predictable 𝓕 S.second S.second_predictable
  first_coefficient := NativePairClock.coefficient_predictable 𝓕 ha hell hb hm S.first S.first_predictable
  second_coefficient := NativePairClock.coefficient_predictable 𝓕 ha hell hb hm S.second S.second_predictable
  additiveInput := NativePairClock.additiveInput 𝓕 μ h hh κ hκ 0 (by norm_num)
  residualInput := NativePairClock.residualInput 𝓕 μ h hh (Λ := 0) (by norm_num) ha hell hb hm S.first S.first_predictable
  controlledAdditiveInput := NativePairClock.additiveInput 𝓕 μ h hh κ hκ Λ hΛ
  controlledResidualInput := NativePairClock.residualInput 𝓕 μ h hh hΛ ha hell hb hm S.second S.second_predictable
  additive_kernel := NativePairClock.additiveInput_zero_ae 𝓕 μ h hh κ hκ
  residual_kernel := NativePairClock.residualInput_zero_ae 𝓕 μ h hh ha hell hb hm S.first S.first_predictable
  controlled_additive_kernel := NativePairClock.additiveInput_ae 𝓕 μ h hh κ hκ Λ hΛ
  controlled_residual_kernel := NativePairClock.residualInput_ae 𝓕 μ h hh hΛ ha hell hb hm S.second S.second_predictable
  first_mild := NativePairMild.first_mild 𝓕 μ h hh hΛ κ hκ ha hell hb hm I₀ I₁ u₀ v₀ S
  second_mild := NativePairMild.second_mild 𝓕 μ h hh hΛ κ hκ ha hell hb hm I₀ I₁ u₀ v₀ S

theorem scaled_holder {H β : ℝ} (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β) :
    ∀ z w,|(NativeClock.rate:ℝ)*a z-(NativeClock.rate:ℝ)*a w|≤
      ((NativeClock.rate:ℝ)*H)*|z-w|^β := by
  intro z w
  have hc0 : 0≤(NativeClock.rate:ℝ) := NativeClock.rate.2
  rw [← mul_sub,abs_mul,abs_of_nonneg hc0]
  exact (mul_le_mul_of_nonneg_left (hholder z w) NativeClock.rate.2).trans_eq (mul_assoc _ _ _).symm

theorem scaled_lipschitz {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ))) :
    LipschitzWith (NativeClock.rate*L) (fun z => (((NativeClock.rate:ℝ)*a z:ℝ):ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hc0 : 0≤(NativeClock.rate:ℝ) := NativeClock.rate.2
  simp only [Complex.ofReal_mul]
  rw [dist_eq_norm,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0]
  rw [← dist_eq_norm]
  change (NativeClock.rate:ℝ)*dist (a z:ℂ) (a w:ℂ)≤((NativeClock.rate:ℝ)*(L:ℝ))*dist z w
  calc
    _≤(NativeClock.rate:ℝ)*((L:ℝ)*dist z w) := mul_le_mul_of_nonneg_left (hLip.dist_le_mul z w) NativeClock.rate.2
    _=_ := by ring

include hh hΛ in
/-- Genuine short-time native construction from the original two
unit-clock integrals and their ordinary BDG bounds. Both native
equations and every literal heat integrand are derived above. -/
theorem exists_pair {H β : ℝ} (hβ : 0<β) (hH : 0≤H)
    (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hsmall : 2*CompanionHeat.picardConstant ((NativeClock.rate:ℝ)*ell)
      ((NativeClock.rate:ℝ)*M) (NativeClock.rate*L)*(h:ℝ)^(1/2:ℝ)≤1/4)
    (hpos : 0<h) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B₀ B₁ : ℝ≥0) (hBDG₀ : StandardTerminalBDG16 I₀ B₀) (hBDG₁ : StandardTerminalBDG16 I₁ B₁) :
    Nonempty (Solution (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
      Λ κ hκ ha hell hb
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀)
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁) u₀ v₀) := by
  obtain ⟨S⟩ := AdditiveResidualPair.exists_pair 𝓕 μ h hh (mul_nonneg NativeClock.rate.2 hΛ)
    ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ)
    (ha.const_mul (NativeClock.rate:ℝ)) (mul_pos NativeClock.rate_pos hell)
    (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hb) hβ (mul_nonneg NativeClock.rate.2 hH)
    (scaled_holder hholder) (scaled_lipschitz hLip) hsmall I₀ I₁ hpos hnull B₀ B₁ hBDG₀ hBDG₁ u₀ v₀
  exact ⟨of_unit 𝓕 μ h hh hΛ κ hκ ha hell hb
    (NonlinearHaarIntegrand.coefficientField_measurable ha hell hb hβ hH hholder) I₀ I₁ u₀ v₀ S⟩

end SHE.NativeAdditiveResidualPair
