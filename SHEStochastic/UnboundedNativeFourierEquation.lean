module

public import SHEStochastic.NativeFourierRemainder
public import SHEStochastic.UnboundedNativeHeatEquation
public import SHEStochastic.NativeMartingaleVersion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedNativeFourierEquation
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)

def growingInput (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  FourierHeatInput.growingInput F (UnboundedL2Localization.state (physical W) N)
    (UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N)
    hG hβ hβ1 μ H (UnboundedL2Localization.history_bound (physical W) μ H N) a n

/-- Each real Fourier coordinate of the actual unbounded native state
satisfies its variation-of-constants equation before every L2 exit.
This is derived from the local positive-heat equation and native Fubini. -/
theorem coordinate_random (ξ : Ω → RealL2) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) (hTH : T < H) (hT : (T : ℝ) < 1) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
      NativeFourierHeatCoordinate.coordinate a n (W T ω) =
        Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) *
          (NativeFourierHeatCoordinate.coordinate a n (ξ ω) +
            (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
              (StoppedItoInputs.stop F μ H T (growingInput F μ H W hW hG hβ hβ1 N a n)) ω) := by
  let U := UnboundedL2Localization.state (physical W) N
  have hU := UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N
  have hbound := UnboundedL2Localization.history_bound (physical W) μ H N
  obtain ⟨Z, hZm, hZe, hZc⟩ := UnboundedHeatContinuity.exists_native_continuous_modification
    F U hU hG hβ hβ1 μ H hbound P e
  have hTnn : T < (1 : ℝ≥0) := by exact_mod_cast hT
  let δ : ℝ≥0 := min (H - T) (1 - T) / 2
  have hδ : 0 < δ := div_pos
    (lt_min (tsub_pos_iff_lt.mpr hTH) (tsub_pos_iff_lt.mpr hTnn)) (by norm_num)
  have hd : δ ≤ min (H - T) (1 - T) := div_le_self zero_le (by norm_num)
  have hTD : T + δ ≤ H := (add_le_add le_rfl (hd.trans (min_le_left _ _))).trans_eq
    (add_tsub_cancel_of_le hTH.le)
  have hTD1 : ((T + δ : ℝ≥0) : ℝ) ≤ 1 := by
    exact_mod_cast (add_le_add le_rfl (hd.trans (min_le_right _ _))).trans_eq
      (add_tsub_cancel_of_le hTnn.le)
  have hs := LocalizedRemainderObservation.state_eq F U hU hG hβ hβ1 μ H hbound P e
    Z hZm hZc (exit W N) (exit_stopping F W hW hcW N)
    (fun p ↦ (hZe p).mono fun _ hz _ ↦ hz)
    T δ hTH.le hT.le hδ hTD hTD1 ξ (W T) (hEquation N T δ hTH.le hT.le hδ hTD hTD1)
  have hc := NativeFourierRemainder.coordinate F U hU hG hβ hβ1 μ H hbound
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) a n T hTH.le hT.le Z hZm hZc hZe
  filter_upwards [hs, hc] with ω hs hc hω
  rw [hs hω, map_add]
  calc
    _ = Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) * NativeFourierHeatCoordinate.coordinate a n (ξ ω) +
        Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) *
          (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
            (StoppedItoInputs.stop F μ H T (growingInput F μ H W hW hG hβ hβ1 N a n)) ω := by
      convert congrArg₂ (fun x y : ℝ ↦ x + y)
        (NativeFourierHeatCoordinate.coordinate_heat a n T.property (ξ ω)) hc using 1 <;> rfl
    _ = _ := by ring

theorem coordinate (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) (hTH : T < H) (hT : (T : ℝ) < 1) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
      NativeFourierHeatCoordinate.coordinate a n (W T ω) =
        Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) *
          (NativeFourierHeatCoordinate.coordinate a n u₀ +
            (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
              (StoppedItoInputs.stop F μ H T (growingInput F μ H W hW hG hβ hβ1 N a n)) ω) := by
  exact coordinate_random F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hcW hEquation N a n T hTH hT

theorem integrating_factor_random (ξ : Ω → RealL2) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) (hTH : T < H) (hT : (T : ℝ) < 1) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
      Real.exp ((T : ℝ) * (n : ℝ) ^ 2) * NativeFourierHeatCoordinate.coordinate a n (W T ω) -
        NativeFourierHeatCoordinate.coordinate a n (ξ ω) =
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (StoppedItoInputs.stop F μ H T (growingInput F μ H W hW hG hβ hβ1 N a n)) ω := by
  filter_upwards [coordinate_random F μ H W hW hG hβ hβ1 P e ξ hcW hEquation N a n T hTH hT] with ω hω hT
  rw [hω hT, ← mul_assoc]
  have he : Real.exp ((T : ℝ) * (n : ℝ) ^ 2) * Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [he, one_mul, add_sub_cancel_left]

/-- Deterministic-initial specialization. -/
theorem integrating_factor (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) (hTH : T < H) (hT : (T : ℝ) < 1) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
      Real.exp ((T : ℝ) * (n : ℝ) ^ 2) * NativeFourierHeatCoordinate.coordinate a n (W T ω) -
        NativeFourierHeatCoordinate.coordinate a n u₀ =
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (StoppedItoInputs.stop F μ H T (growingInput F μ H W hW hG hβ hβ1 N a n)) ω := by
  exact integrating_factor_random F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hcW hEquation N a n T hTH hT

/-- The integrating factor of an original Fourier mode agrees locally
with an actual adapted continuous native martingale. Its construction
uses the existing integral, not an extra stochastic input block. -/
theorem exists_martingale_random (ξ : Ω → RealL2) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (M · ω)) ∧
      StronglyAdapted F M ∧ StronglyMeasurable[F.predictable] (Function.uncurry M) ∧
      Martingale M F μ ∧
      (∀ T, M T =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T (growingInput F μ H W hW hG hβ hβ1 N a n))) ∧
      ∀ (T : ℝ≥0), T < H → (T : ℝ) < 1 →
        ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
          Real.exp ((T : ℝ) * (n : ℝ) ^ 2) * NativeFourierHeatCoordinate.coordinate a n (W T ω) -
            NativeFourierHeatCoordinate.coordinate a n (ξ ω) = M T ω := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  obtain ⟨M, hc, ha, hp, hm, hr⟩ := NativeMartingaleVersion.exists_version P e hnull
    (growingInput F μ H W hW hG hβ hβ1 N a n)
  refine ⟨M, hc, ha, hp, hm, hr, ?_⟩
  intro T hTH hT
  filter_upwards [integrating_factor_random F μ H W hW hG hβ hβ1 P e ξ hcW hEquation N a n T hTH hT, hr T]
    with ω hω hr hBefore
  exact (hω hBefore).trans hr.symm

/-- Deterministic-initial specialization. -/
theorem exists_martingale (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (M · ω)) ∧
      StronglyAdapted F M ∧ StronglyMeasurable[F.predictable] (Function.uncurry M) ∧
      Martingale M F μ ∧
      (∀ T, M T =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T (growingInput F μ H W hW hG hβ hβ1 N a n))) ∧
      ∀ (T : ℝ≥0), T < H → (T : ℝ) < 1 →
        ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
          Real.exp ((T : ℝ) * (n : ℝ) ^ 2) * NativeFourierHeatCoordinate.coordinate a n (W T ω) -
            NativeFourierHeatCoordinate.coordinate a n u₀ = M T ω := by
  exact exists_martingale_random F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hcW hnull hEquation N a n

end SHEStochastic.UnboundedNativeFourierEquation
