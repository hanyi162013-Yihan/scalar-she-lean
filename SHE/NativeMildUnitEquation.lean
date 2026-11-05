module

public import SHE.NativeFirstMildData
public import SHE.ClockedOriginalIntegral
public import SHE.TimeDilationPathPull
public import SHE.NativePairKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeMildUnitEquation
open MeasureTheory Set PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance nativeMildUnitEquation_finite : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance nativeMildUnitEquation_stateSigma : MeasurableSpace StateL2:=borel _
local instance nativeMildUnitEquation_stateBorel : BorelSpace StateL2:=⟨rfl⟩
local instance nativeMildUnitEquation_nativeSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeMildUnitEquation_nativeBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeMildUnitEquation_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeMildUnitEquation_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable (κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
local notation "rate"=>NativeClock.rate
local notation "ratePos"=>NativeClock.rate_pos
variable (J₀ J₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) (filtration 𝓕 (clock rate ratePos)) μ (rate*h))
variable (u₀ : StateL2)

variable (S : NativeFirstMildData.Data 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀)
local notation "U"=>pullPath rate ratePos S.value
local notation "g"=>coefficientFunction (ha.const_mul (rate:ℝ)) (mul_pos ratePos hell)
  (HaarFieldScaling.scaled_bounds ratePos hb) U
local notation "hg"=>NativeFirstMildData.unit_coefficient_predictable 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀ S
local notation "I₀"=>inverseIntegral 𝓕 μ rate ratePos h J₀
local notation "I₁"=>inverseIntegral 𝓕 μ rate ratePos h J₁

theorem residual_terminal (t : ℝ≥0) (ht : t≤h) :
    J₁.integral (S.residualInput (clock rate ratePos t))=
      DampedFixedIntegral.value 𝓕 μ h hh (Λ:=0) (by norm_num) (mul_pos ratePos hell)
        (mul_nonneg rate.2 (hell.le.trans ((hb 0).1.trans (hb 0).2))) g hg I₁ t ht := by
  have hfg:=ClockedPairFields.unitField_coefficient rate ratePos ha hell hb U
  rw [path_pullPath] at hfg
  have hh':=ClockedPairIntegral.original_terminal_eq 𝓕 μ rate ratePos h hh (Λ:=0) (by norm_num)
    hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (coefficientFunction ha hell hb S.value) S.coefficient g hg hfg J₁ t ht
    (S.residualInput (clock rate ratePos t)) (by
      filter_upwards [S.residual_kernel (clock rate ratePos t) (mul_le_mul_of_nonneg_left ht rate.2)] with p hp
      rw [hp]
      simp only [ClockedHaarIntegral.kernel,NativeHeatObservation.kernel,NativeClock.rate_coe,neg_zero,zero_mul,Real.exp_zero,one_smul])
  simpa only [mul_zero] using hh'

theorem additive_terminal (t : ℝ≥0) (ht : t≤h) :
    J₀.integral (S.additiveInput (clock rate ratePos t))=
      DampedFixedIntegral.value 𝓕 μ h hh (Λ:=0) (by norm_num) (mul_pos ratePos hκ)
        (mul_nonneg rate.2 hκ.le)
        (fun _=>AdditiveHaarForcing.constantField ((rate:ℝ)*κ) (mul_pos ratePos hκ))
        stronglyMeasurable_const I₀ t ht := by
  have hh':=ClockedPairIntegral.original_terminal_eq 𝓕 μ rate ratePos h hh (Λ:=0) (by norm_num)
    hκ hκ.le (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    (fun _=>AdditiveHaarForcing.constantField ((rate:ℝ)*κ) (mul_pos ratePos hκ))
    stronglyMeasurable_const (ClockedPairFields.unitField_constant rate ratePos κ hκ) J₀ t ht
    (S.additiveInput (clock rate ratePos t)) (by
      filter_upwards [S.additive_kernel (clock rate ratePos t) (mul_le_mul_of_nonneg_left ht rate.2)] with p hp
      rw [hp]
      simp only [ClockedHaarIntegral.kernel,NativeHeatObservation.kernel,NativeClock.rate_coe,neg_zero,zero_mul,Real.exp_zero,one_smul])
  simpa only [mul_zero] using hh'

/-- The supplied native first solution obeys the literal unit-clock
mild equation after an exact inverse clock change, on the original
noise coordinates. No native mild equation is assumed in unit units. -/
theorem unit_mild (t : ℝ≥0) (ht : t≤h) :
    U t=ᵐ[μ] fun ω=>RealHeat.realHeat (t:ℝ) u₀+
      AdditiveResidualPair.additiveTerminal 𝓕 μ h hh (Λ:=0) (by norm_num)
        ((rate:ℝ)*κ) (mul_pos ratePos hκ) I₀ t ht ω+
      DampedFixedIntegral.value 𝓕 μ h hh (Λ:=0) (by norm_num) (mul_pos ratePos hell)
        (mul_nonneg rate.2 (hell.le.trans ((hb 0).1.trans (hb 0).2))) g hg I₁ t ht ω := by
  have hA:=additive_terminal 𝓕 μ h hh κ hκ ha hell hb J₀ J₁ u₀ S t ht
  have hR:=residual_terminal 𝓕 μ h hh κ hκ ha hell hb J₀ J₁ u₀ S t ht
  have hheat : NativeHeatObservation.heat (clock rate ratePos t:ℝ)=RealHeat.realHeat (t:ℝ) := by
    have he:=NativeClock.heat_time (clock rate ratePos t)
    simpa only [NativeClock.time,OrderIso.symm_apply_apply] using he.symm
  filter_upwards [S.mild (clock rate ratePos t) (mul_le_mul_of_nonneg_left ht rate.2)] with ω hω
  change S.value (clock rate ratePos t) ω=_
  rw [hω,hheat]
  exact congrArg₂ (fun a b : StateL2=>a+b)
    (congrArg₂ (fun a b : StateL2=>a+b) rfl (congrArg (fun z : Lp StateL2 2 μ=>z ω) hA))
    (congrArg (fun z : Lp StateL2 2 μ=>z ω) hR)

end SHE.NativeMildUnitEquation
