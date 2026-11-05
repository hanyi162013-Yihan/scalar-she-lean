module

public import SHEStochastic.HeatRowParameterIntegration
public import SHEStochastic.HeatParameterPullback

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.HeatRowPhysicalIntegration
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback UnboundedHeatJointMoments
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)

theorem input_point (t : ShortTime) (ht : t.val ≤ H) (a : HeatCircle) :
    parameterInput F U hU hG hβ hβ1 μ H hbound (point t a) =
      UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H ⟨t.val, t.property.1⟩ ht t.property.2 a hbound := by
  have he : time H (point t a) = (⟨t.val, t.property.1⟩ : ℝ≥0) :=
    NNReal.eq (time_point H t a ht)
  simp only [parameterInput, he, center_point]

theorem integrable_input (t : ShortTime) (ht : t.val ≤ H)
    (ρ : Measure HeatCircle) [IsFiniteMeasure ρ] :
    Integrable (fun a : HeatCircle ↦ UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H
      ⟨t.val, t.property.1⟩ ht t.property.2 a hbound) ρ := by
  have hp : Measurable (point t) := measurable_point.comp (measurable_const.prodMk measurable_id)
  have hK := HeatRowParameterIntegration.integrable_input F U hU hG hβ hβ1 μ H hbound (ρ.map (point t))
  have hh := (integrable_map_measure hK.aestronglyMeasurable hp.aemeasurable).mp hK
  exact hh.congr (Eventually.of_forall (input_point F U hU hG hβ hβ1 μ H hbound t ht))

/-- Fubini for the actual physical spatial section, under any finite
spatial measure (in particular a positive heat-kernel weight). The
measurable circle representative is handled by measure pushforward;
no continuity at its artificial seam is required. -/
theorem integral_ae
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (t : ShortTime) (ht : t.val ≤ H) (ρ : Measure HeatCircle) [IsFiniteMeasure ρ]
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (parameterInput F U hU hG hβ hβ1 μ H hbound p)) :
    J.integral (∫ a : HeatCircle, UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H
      ⟨t.val, t.property.1⟩ ht t.property.2 a hbound ∂ρ) =ᵐ[μ]
      fun ω ↦ ∫ a : HeatCircle, Y (point t a) ω ∂ρ := by
  have hp : Measurable (point t) := measurable_point.comp (measurable_const.prodMk measurable_id)
  let ν : Measure Parameter := ρ.map (point t)
  have hK := HeatRowParameterIntegration.integrable_input F U hU hG hβ hβ1 μ H hbound ν
  have hleft : (∫ p, parameterInput F U hU hG hβ hβ1 μ H hbound p ∂ν) =
      ∫ a : HeatCircle, UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H
        ⟨t.val, t.property.1⟩ ht t.property.2 a hbound ∂ρ := by
    rw [show ν = ρ.map (point t) from rfl, integral_map hp.aemeasurable hK.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall (input_point F U hU hG hβ hβ1 μ H hbound t ht))
  have hright (ω : Ω) : (∫ p, Y p ω ∂ν) = ∫ a : HeatCircle, Y (point t a) ω ∂ρ :=
    integral_map hp.aemeasurable (hc ω).aestronglyMeasurable_of_compactSpace
  have hh := HeatRowParameterIntegration.integral_ae F U hU hG hβ hβ1 μ H hbound J ν Y hm hc he
  rw [hleft] at hh
  exact hh.mono fun ω hω ↦ hω.trans (hright ω)

/-- Signed bounded continuous spatial weights, including real and
imaginary Fourier weights, commute with the SAME native stochastic
integral. Joint integrability follows from the proved L2 input bounds. -/
theorem weighted_integral_ae
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (t : ShortTime) (ht : t.val ≤ H) (ρ : Measure HeatCircle) [IsFiniteMeasure ρ]
    (w : C(HeatCircle, ℝ)) (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (parameterInput F U hU hG hβ hβ1 μ H hbound p)) :
    J.integral (∫ a : HeatCircle, w a • UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H
      ⟨t.val, t.property.1⟩ ht t.property.2 a hbound ∂ρ) =ᵐ[μ]
      fun ω ↦ ∫ a : HeatCircle, w a * Y (point t a) ω ∂ρ := by
  let K := fun a : HeatCircle ↦ UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H
    ⟨t.val, t.property.1⟩ ht t.property.2 a hbound
  have hK : Integrable K ρ := integrable_input F U hU hG hβ hβ1 μ H hbound t ht ρ
  have hwK : Integrable (fun a ↦ w a • K a) ρ := hK.bdd_smul (𝕜 := ℝ) (φ := w) ‖w‖
    w.continuous.measurable.aestronglyMeasurable (Eventually.of_forall w.norm_coe_le_norm)
  have hy : Measurable (fun z : HeatCircle × Ω ↦ Y (point t z.1) z.2) :=
    (measurable_physical Y hm hc).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  let raw := fun z : HeatCircle × Ω ↦ w z.1 * Y (point t z.1) z.2
  have hraw : AEStronglyMeasurable raw (ρ.prod μ) :=
    ((w.continuous.measurable.comp measurable_fst).mul hy).aestronglyMeasurable
  have hRep : ∀ᵐ a ∂ρ, J.integral (w a • K a) =ᵐ[μ] fun ω ↦ raw (a, ω) := by
    apply Eventually.of_forall
    intro a
    have ha := he (point t a)
    rw [input_point F U hU hG hβ hβ1 μ H hbound t ht a] at ha
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (w a) (J.integral (K a)), ha] with ω hs hy
    exact hs.trans (congrArg (fun z : ℝ ↦ w a * z) hy.symm)
  have hi := LpVersionIntegration.integrable μ ρ (fun a ↦ J.integral (w a • K a))
    (J.integral.toContinuousLinearMap.integrable_comp hwK) raw hraw hRep
  exact TerminalItoFubini.integral_ae F μ H J ρ (fun a ↦ w a • K a) hwK raw hi hRep

end SHEStochastic.HeatRowPhysicalIntegration
