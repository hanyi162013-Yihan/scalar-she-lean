module

public import SHEStochastic.GlobalHeatRowParameterIntegration
public import SHE.TerminalItoFubini
public import SHEStochastic.LpVersionIntegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.GlobalHeatRowPhysicalIntegration
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback UnboundedGlobalJointMoments
open scoped NNReal ENNReal

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

def unitTime (H : ℝ≥0) (hH : 0<H) (T : ℝ≥0) (hTH : T≤H) : ShortTime :=
  GlobalHeatParameter.normalized H hH ⟨T,T.property,hTH⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : 0<H) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)

theorem input_point (T : ℝ≥0) (hTH : T≤H) (a : HeatCircle) :
    parameterInput F U hU hG hβ hβ1 μ H hbound (point (unitTime H hH T hTH) a)=
      UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H T hTH a hbound := by
  have he : GlobalHeatParameter.time H (point (unitTime H hH T hTH) a)=T :=
    NNReal.eq (GlobalHeatParameter.time_point H hH ⟨T,T.property,hTH⟩ a)
  simp only [parameterInput,he,center_point]

include hH in
theorem integrable_input (T : ℝ≥0) (hTH : T≤H) (ρ : Measure HeatCircle) [IsFiniteMeasure ρ] :
    Integrable (fun a : HeatCircle ↦ UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H T hTH a hbound) ρ := by
  have hp : Measurable (point (unitTime H hH T hTH)) := measurable_point.comp (measurable_const.prodMk measurable_id)
  have hK := GlobalHeatRowParameterIntegration.integrable_input F U hU hG hβ hβ1 μ H hbound
    (ρ.map (point (unitTime H hH T hTH)))
  have hh := (integrable_map_measure hK.aestronglyMeasurable hp.aemeasurable).mp hK
  exact hh.congr (Eventually.of_forall (input_point F U hU hG hβ hβ1 μ H hH hbound T hTH))

/-- Stochastic Fubini for full-horizon physical heat sections. The
native integral, parameter versions and ordinary Bochner inputs are
identified explicitly; no Fubini premise is added to the solution. -/
theorem integral_ae
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2*Real.pi))) (E := ℝ) F μ H)
    (T : ℝ≥0) (hTH : T≤H) (ρ : Measure HeatCircle) [IsFiniteMeasure ρ]
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p)) (hc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (he : ∀ p, Y p=ᵐ[μ] J.integral (parameterInput F U hU hG hβ hβ1 μ H hbound p)) :
    J.integral (∫ a : HeatCircle, UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H T hTH a hbound ∂ρ)=ᵐ[μ]
      fun ω ↦ ∫ a : HeatCircle, Y (point (unitTime H hH T hTH) a) ω ∂ρ := by
  let K := fun a : HeatCircle ↦ UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H T hTH a hbound
  have hK : Integrable K ρ := integrable_input F U hU hG hβ hβ1 μ H hH hbound T hTH ρ
  let raw := fun z : HeatCircle×Ω ↦ Y (point (unitTime H hH T hTH) z.1) z.2
  have hraw : Measurable raw :=
    (measurable_physical Y hm hc).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hRep : ∀ᵐ a ∂ρ, J.integral (K a)=ᵐ[μ] fun ω ↦ raw (a,ω) := by
    apply Eventually.of_forall
    intro a
    have hh := he (point (unitTime H hH T hTH) a)
    rw [input_point F U hU hG hβ hβ1 μ H hH hbound T hTH a] at hh
    exact hh.symm
  have hi := LpVersionIntegration.integrable μ ρ (fun a ↦ J.integral (K a))
    (J.integral.toContinuousLinearMap.integrable_comp hK) raw hraw.aestronglyMeasurable hRep
  exact TerminalItoFubini.integral_ae F μ H J ρ K hK raw hi hRep

/-- Signed bounded continuous spatial weights, including real and
imaginary Fourier weights, commute with the SAME native stochastic
integral. Joint integrability follows from the proved L2 input bounds. -/
theorem weighted_integral_ae
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (T : ℝ≥0) (hTH : T≤H) (ρ : Measure HeatCircle) [IsFiniteMeasure ρ]
    (w : C(HeatCircle, ℝ)) (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (parameterInput F U hU hG hβ hβ1 μ H hbound p)) :
    J.integral (∫ a : HeatCircle, w a • UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H
      T hTH a hbound ∂ρ) =ᵐ[μ]
      fun ω ↦ ∫ a : HeatCircle, w a * Y (point (unitTime H hH T hTH) a) ω ∂ρ := by
  let K := fun a : HeatCircle ↦ UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H
    T hTH a hbound
  have hK : Integrable K ρ := integrable_input F U hU hG hβ hβ1 μ H hH hbound T hTH ρ
  have hwK : Integrable (fun a ↦ w a • K a) ρ := hK.bdd_smul (𝕜 := ℝ) (φ := w) ‖w‖
    w.continuous.measurable.aestronglyMeasurable (Eventually.of_forall w.norm_coe_le_norm)
  have hy : Measurable (fun z : HeatCircle × Ω ↦ Y (point (unitTime H hH T hTH) z.1) z.2) :=
    (measurable_physical Y hm hc).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  let raw := fun z : HeatCircle × Ω ↦ w z.1 * Y (point (unitTime H hH T hTH) z.1) z.2
  have hraw : AEStronglyMeasurable raw (ρ.prod μ) :=
    ((w.continuous.measurable.comp measurable_fst).mul hy).aestronglyMeasurable
  have hRep : ∀ᵐ a ∂ρ, J.integral (w a • K a) =ᵐ[μ] fun ω ↦ raw (a, ω) := by
    apply Eventually.of_forall
    intro a
    have ha := he (point (unitTime H hH T hTH) a)
    rw [input_point F U hU hG hβ hβ1 μ H hH hbound T hTH a] at ha
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (w a) (J.integral (K a)), ha] with ω hs hy
    exact hs.trans (congrArg (fun z : ℝ ↦ w a * z) hy.symm)
  have hi := LpVersionIntegration.integrable μ ρ (fun a ↦ J.integral (w a • K a))
    (J.integral.toContinuousLinearMap.integrable_comp hwK) raw hraw hRep
  exact TerminalItoFubini.integral_ae F μ H J ρ (fun a ↦ w a • K a) hwK raw hi hRep

end SHEStochastic.GlobalHeatRowPhysicalIntegration
