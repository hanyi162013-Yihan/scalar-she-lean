module

public import SHE.VolterraProcess
public import SHE.DampedNonlinearConvolution
public import SHE.HeatInitialProcess

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledForcing
open MeasureTheory Set PredictableL2 LowBands
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2 := borel StateL2
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) {Λ : ℝ} (hΛ : 0 ≤ Λ)

def initialFunction (u₀ : StateL2) (p : ℝ≥0 × Ω) : StateL2 :=
  Real.exp (-Λ*(p.1:ℝ)) • RealHeat.realHeat (p.1:ℝ) u₀

theorem initial_predictable (u₀ : StateL2) :
    StronglyMeasurable[𝓕.predictable] (initialFunction (Λ := Λ) u₀ (Ω := Ω)) := by
  exact ((Real.measurable_exp.comp (measurable_const.mul (PredictableClock.real_time_measurable 𝓕))).stronglyMeasurable).smul
    (HeatInitialProcess.predictable 𝓕 u₀)

include hΛ in
theorem initial_memLp (u₀ : StateL2) :
    @MemLp _ _ 𝓕.predictable _ _ (initialFunction (Λ := Λ) u₀ (Ω := Ω)) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have : IsFiniteMeasure (energyMeasure μ h) := by dsimp only [energyMeasure]; infer_instance
  apply MemLp.of_bound (initial_predictable 𝓕 u₀).aestronglyMeasurable ‖u₀‖
  apply Filter.Eventually.of_forall
  intro p
  have he : Real.exp (-Λ*(p.1:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [p.1.2])
  rw [initialFunction,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
    (by simpa only [one_mul] using RealHeat.realHeat_contraction p.1 u₀)

def initial (u₀ : StateL2) : Process (E := StateL2) 𝓕 μ h :=
  (initial_memLp 𝓕 μ h hΛ u₀).toLp (initialFunction (Λ := Λ) u₀)

theorem initial_ae (u₀ : StateL2) : initial 𝓕 μ h hΛ u₀ =ᵐ[energyMeasure μ h]
    initialFunction (Λ := Λ) u₀ :=
  ae_eq_of_ae_eq_trim (initial_memLp 𝓕 μ h hΛ u₀).coeFn_toLp

variable (U : ℝ≥0 → Ω → StateL2)
variable (haU : StronglyAdapted 𝓕 U) (hcU : ∀ ω,Continuous (fun t => U t ω))
variable (u : Process (E := StateL2) 𝓕 μ h)
variable (hu : u =ᵐ[energyMeasure μ h] Function.uncurry U)

/-- The literal forcing for the controlled equation dV=ΔVdt+
Λ(U−V)dt+√a(V)dW, constructed as an actual predictable L² process. -/
def forcing (u₀ : StateL2) : Process (E := StateL2) 𝓕 μ h :=
  initial 𝓕 μ h hΛ u₀+Λ • VolterraProcess.process 𝓕 μ h hΛ U haU hcU u hu

theorem forcing_ae (u₀ : StateL2) : forcing 𝓕 μ h hΛ U haU hcU u hu u₀ =ᵐ[energyMeasure μ h]
    (fun p : ℝ≥0 × Ω => Real.exp (-Λ*(p.1:ℝ)) • RealHeat.realHeat (p.1:ℝ) u₀+
      Λ • VolterraPath.value Λ (fun s => U s p.2) p.1) := by
  have hadd := ae_eq_of_ae_eq_trim (Lp.coeFn_add (initial 𝓕 μ h hΛ u₀)
    (Λ • VolterraProcess.process 𝓕 μ h hΛ U haU hcU u hu))
  have hsmul := ae_eq_of_ae_eq_trim (Lp.coeFn_smul Λ (VolterraProcess.process 𝓕 μ h hΛ U haU hcU u hu))
  filter_upwards [hadd,hsmul,initial_ae 𝓕 μ h hΛ u₀,
    VolterraProcess.process_ae 𝓕 μ h hΛ U haU hcU u hu] with p hp hs hi hv
  change (initial 𝓕 μ h hΛ u₀+Λ • VolterraProcess.process 𝓕 μ h hΛ U haU hcU u hu) p=_
  rw [hp]
  simp only [Pi.add_apply,Pi.smul_apply,RingHom.id_apply] at hs ⊢
  rw [hs,hi,hv]
  rfl

include haU hcU hu in
/-- For every actual continuous adapted finite-energy input, the
controlled companion has a unique short-time predictable L² solution.
Its forcing and damped convolution are both constructed here. -/
theorem exists_unique_controlled {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
    (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
    (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ))) (hh : (h:ℝ) ≤ 1)
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (u₀ : StateL2) :
    ∃! v : Process (E := StateL2) 𝓕 μ h,
      v=forcing 𝓕 μ h hΛ U haU hcU u hu u₀+
        DampedNonlinearConvolution.map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I v :=
  DampedNonlinearConvolution.exists_unique_forced 𝓕 μ h hh hΛ ha hell hb hβ hH hholder
    hLip hsmall I (forcing 𝓕 μ h hΛ U haU hcU u hu u₀)

end SHE.ControlledForcing
