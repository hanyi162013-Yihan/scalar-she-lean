module

public import SHEStochastic.GlobalBoundedFourierRecognition
public import SHEStochastic.GlobalMildUniformExit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalBoundedMildUniformRegularity
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open HeatParameterCover HeatParameterCoordinates BoundedHeatCoefficientLift StoppedPathPasting
open GlobalBoundedHeatCoefficientLift GlobalHeatParameter
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)

theorem initial_zero (Y : Ω → C(Parameter, ℝ))
    (he : ∀ p, (fun sample ↦ Y sample p) =ᵐ[μ] J.integral
      (GlobalBoundedHeatCoefficientLift.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        (GlobalHeatParameter.time H p) (GlobalHeatParameter.time_le_horizon H p) (center p))) :
    ∀ᵐ sample ∂μ, ∀ p, Y sample (zeroTime p) = 0 := by
  have hz (p : Parameter) : (fun sample ↦ Y sample (zeroTime p)) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    have hi : GlobalBoundedHeatCoefficientLift.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        (GlobalHeatParameter.time H (zeroTime p)) (GlobalHeatParameter.time_le_horizon H (zeroTime p))
        (center (zeroTime p)) = 0 := by
      simp only [GlobalBoundedHeatCoefficientLift.input]
      exact UnboundedFiniteHorizonInput.input_zero F _ _ (projection_holder B)
        (by norm_num) (by norm_num) μ H _ _ _ _ (GlobalHeatParameter.zeroTime_time H p)

    have hh := he (zeroTime p)
    rw [hi, map_zero] at hh
    exact hh.trans (Lp.coeFn_zero _ _ _)
  have hc : ∀ᵐ sample ∂μ, Continuous (fun p ↦ Y sample (zeroTime p)) :=
    Filter.Eventually.of_forall fun sample ↦ (Y sample).continuous.comp continuous_zeroTime
  have hh := indistinguishable_of_edist_modification hc (Filter.Eventually.of_forall fun _ ↦ continuous_const)
    (fun p ↦ (hz p).mono fun _ hp ↦ edist_eq_zero.mpr hp)
  exact hh.mono fun sample hs p ↦ edist_eq_zero.mp (hs p)

/-- Raw native mild laws already have the uniform-norm regularity
needed to recover exit times after pasting. No completion, stochastic
factorization input or spatially continuous initial data is required. -/
theorem regularity (ξ : Ω → RealL2) (u : RealL2) (hξ : ξ =ᵐ[μ] fun _ ↦ u)
    (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (M : ℝ) (hM : 0 ≤ M)
    (hu : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u = ENNReal.ofReal M)
    (hMild : GlobalBoundedFourierRecognition.HasClosedVersion F μ H W hW hG hβ hβ1 B hb hH J ξ) :
    ∀ᵐ sample ∂μ,
      Continuous (fun t : Time H ↦ L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))
        (NativeContinuousPath.path H W hcW sample t)) ∧
      ∀ t : Time H, L2ExtendedUniformNorm.value (haarAddCircle (T := 1))
        (NativeContinuousPath.path H W hcW sample t) ≠ ⊤ := by
  obtain ⟨Y, hm, he, hs⟩ := hMild
  filter_upwards [initial_zero F μ H W hW hG hβ hβ1 B hb J Y he, hs, hξ] with sample hz hs hξ
  apply GlobalMildUniformExit.regular_path H hH (NativeContinuousPath.path H W hcW sample) u M hM hu (Y sample) hz
  intro t
  let T : ℝ≥0 := t.val.toNNReal
  have ht : (T : ℝ) = t.val := Real.coe_toNNReal _ t.property.1
  have hTH : T ≤ H := by change (T : ℝ) ≤ H; rw [ht]; exact t.property.2
  have hj : GlobalHeatRowPhysicalIntegration.unitTime H hH T hTH = GlobalHeatParameter.normalized H hH t := by
    apply Subtype.ext
    exact congrArg (fun r : ℝ ↦ r / (H : ℝ)) ht
  have hh := congrArg NativePhysicalState.push (hs T hTH)
  rw [hξ] at hh
  have hp := NativeRemainderObservation.push_mild (r := (T : ℝ)) T.property u (Y sample)
    (GlobalHeatRowPhysicalIntegration.unitTime H hH T hTH)
  rw [hj] at hh hp
  exact (hh.trans hp).trans (congrArg (fun r : ℝ ↦
    PhysicalHeatState.state r (NativeHeatObservation.embed u) +
      PhysicalHeatParameterSection.value 2 (Y sample) (GlobalHeatParameter.normalized H hH t)) ht)

end SHEStochastic.GlobalBoundedMildUniformRegularity
