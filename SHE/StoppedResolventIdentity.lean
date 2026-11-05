module

public import SHE.StoppedInputResolvent
public import SHE.TerminalItoFubini

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.StoppedInputResolvent
open MeasureTheory Set Filter PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable (v : Process (E := C) 𝓕 μ h)

def damped {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0) : Process (E := C) 𝓕 μ h :=
  PredictableContraction.weighted 𝓕 μ h (PredictableDamping.weight Λ (t:ℝ))
    (PredictableDamping.weight_predictable 𝓕 Λ (t:ℝ)) (PredictableDamping.weight_bound hΛ (t:ℝ))
    (stop 𝓕 μ h (t:ℝ) v)

theorem damped_ae_trim {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0) :
    damped 𝓕 μ h v hΛ t=ᵐ[(energyMeasure μ h).trim (predictable_le_product 𝓕)]
      fun p => PredictableDamping.weight Λ (t:ℝ) p • stop 𝓕 μ h (t:ℝ) v p :=
  (PredictableContraction.weighted_memLp 𝓕 μ h (PredictableDamping.weight Λ (t:ℝ))
    (PredictableDamping.weight_predictable 𝓕 Λ (t:ℝ)) (PredictableDamping.weight_bound hΛ (t:ℝ))
    (stop 𝓕 μ h (t:ℝ) v)).coeFn_toLp

/-- Exact stopped-row Volterra resolvent in the genuine predictable L²
space. Its parameter integral, clipping, and exponential mass have all
been integrated, rather than supplied as an operator identity. -/
theorem resolvent {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0) :
    Λ • (∫ s,family 𝓕 μ h v Λ t s ∂timeMeasure t)=
      stop 𝓕 μ h (t:ℝ) v-damped 𝓕 μ h v hΛ t := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul Λ (∫ s,family 𝓕 μ h v Λ t s ∂timeMeasure t),
    integral_family_ae 𝓕 μ h v hΛ t,
    Lp.coeFn_sub (stop 𝓕 μ h (t:ℝ) v) (damped 𝓕 μ h v hΛ t),
    damped_ae_trim 𝓕 μ h v hΛ t,StoppedInputParameter.stop_ae_trim 𝓕 μ h v (t:ℝ)]
    with p hsmul hi hsub hd hs
  rw [hsmul,hsub]
  change Λ • (∫ s,family 𝓕 μ h v Λ t s ∂timeMeasure t) p=
    stop 𝓕 μ h (t:ℝ) v p-damped 𝓕 μ h v hΛ t p
  rw [hi,integral_rawFamily,smul_smul,ExponentialStopMass.mul_mass,hd,hs]
  by_cases hp : p.1<t
  · rw [if_pos hp,Set.indicator_of_mem (show p∈before (Ω := Ω) (t:ℝ) from hp),
      PredictableDamping.weight_eq (show (p.1:ℝ)≤(t:ℝ) from hp.le),sub_smul,one_smul]
  · rw [if_neg hp,Set.indicator_of_notMem (show p∉before (Ω := Ω) (t:ℝ) from hp),
      zero_smul,smul_zero,sub_self]

theorem integral_resolvent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ≥0) :
    Λ • (∫ s,I.integral (family 𝓕 μ h v Λ t s) ∂timeMeasure t)=
      I.integral (stop 𝓕 μ h (t:ℝ) v)-I.integral (damped 𝓕 μ h v hΛ t) := by
  have he := congrArg I.integral (resolvent 𝓕 μ h v hΛ t)
  rw [map_smul,map_sub,TerminalItoFubini.integral_comm] at he
  exact he

end SHE.StoppedInputResolvent
