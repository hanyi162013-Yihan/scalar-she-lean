module

public import SHEStochastic.HeatParameterCover
public import SHEStochastic.BDGKolmogorov
public import BrownianMotion.Continuity.KolmogorovChentsov

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.HeatParameterContinuity
open MeasureTheory ProbabilityTheory HeatParameterCover
open scoped NNReal ENNReal

/-- The public Chentsov theorem on the actual compact two-dimensional
parameter domain. The moment estimate, not continuity, is the input. -/
theorem exists_continuous_modification {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Parameter → Ω → E)
    (hX : ∀ t, Measurable (X t)) (m : ℕ) (hm : 0 < m)
    {q : ℝ} (hq : 2 < q) (M : ℝ≥0)
    (hMoment : ∀ s t, (∫⁻ ω, ENNReal.ofReal (‖X s ω - X t ω‖ ^ m) ∂μ) ≤
      (M : ℝ≥0∞) * edist s t ^ q) :
    ∃ Y : Parameter → Ω → E, (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[μ] X t) ∧ ∀ ω, Continuous (fun t ↦ Y t ω) := by
  have hk := BDGKolmogorov.of_nat_moments μ X hX m hm q (by linarith) M hMoment
  obtain ⟨Y, hYm, hYe, hYh⟩ := ProbabilityTheory.exists_modification_holder
    parameter_cover isOpen_univ hk.IsAEKolmogorovProcess (by norm_num) (by norm_num) hq
  refine ⟨Y, hYm, fun t ↦ hYe t (Set.mem_univ t), fun ω ↦ ?_⟩
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨r, hr0, hrq⟩ := exists_between (div_pos (sub_pos.mpr hq) hp)
  let r' : ℝ≥0 := ⟨r, hr0.le⟩
  obtain ⟨K, hK⟩ := hYh r' (by exact_mod_cast hr0) hrq ω
  exact continuousOn_univ.mp (hK.continuousOn (by exact_mod_cast hr0))

/-- The common dyadic-order selection step for native convolution
continuity. Every positive base increment exponent is sufficient. -/
theorem exists_of_dyadic_moments {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Parameter → Ω → E)
    (hX : ∀ t, Measurable (X t)) (q : ℝ) (hq : 0<q)
    (M : ℕ → ℝ≥0∞) (hM : ∀ k, M k≠⊤)
    (hMoment : ∀ k s t, (∫⁻ ω, ENNReal.ofReal (‖X s ω-X t ω‖^(2*2^k)) ∂μ)≤
      M k*edist s t^(q*(2^k:ℕ))) :
    ∃ Y : Parameter → Ω → E, (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t=ᵐ[μ] X t) ∧ ∀ ω, Continuous (fun t ↦ Y t ω) := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (2/q) (by norm_num : (1:ℝ)<2)
  have hkq : 2<q*(2^k:ℕ) := by
    have hh := (div_lt_iff₀ hq).mp hk
    push_cast
    nlinarith
  apply exists_continuous_modification μ X hX (2*2^k) (by positivity) hkq (M k).toNNReal
  intro s t
  rw [ENNReal.coe_toNNReal (hM k)]
  exact hMoment k s t

end SHEStochastic.HeatParameterContinuity
