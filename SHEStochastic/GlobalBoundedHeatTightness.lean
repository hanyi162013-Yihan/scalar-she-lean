module

public import SHEStochastic.GlobalBoundedHeatCoefficientLift
public import SHEStochastic.UnboundedGlobalHeatContinuity
public import SHEStochastic.KolmogorovFieldTightness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalBoundedHeatTightness
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open HeatParameterCover HeatParameterCoordinates BoundedHeatCoefficientLift GlobalBoundedHeatCoefficientLift
open scoped ENNReal NNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (U : ℕ → ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : ∀ k, StronglyMeasurable[F.predictable] (U k))
  {G : ℕ → E → V} {C : ℕ → ℝ≥0} {β : ℝ≥0}
  (hG : ∀ k, HolderWith (C k) β (G k)) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ≥0) (hb : ∀ k z, ‖G k z‖ ≤ B)
  {ι : Type*} [Countable ι] [DecidableEq ι] (P : ℕ → FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

/-- Actual continuous native heat-convolution versions have uniformly
tight laws whenever the coefficients share a uniform bound. Neither
solution L2 localization nor uniform Lipschitz constants are premises. -/
theorem exists_tight_versions_varying :
    ∃ Y : ℕ → Ω → C(Parameter, ℝ), (∀ k, Measurable (Y k)) ∧
      (∀ k p, (fun sample ↦ Y k sample p) =ᵐ[μ]
        (FiniteCylindricalIto.terminalIto (P k).toCoordinates e).integral
          (GlobalBoundedHeatCoefficientLift.input F (U k) (hU k) (hG k) hβ hβ1 B (hb k) μ H (GlobalHeatParameter.time H p)
            (GlobalHeatParameter.time_le_horizon H p) (center p))) ∧
      IsTightMeasureSet (Set.range (fun k ↦ μ.map (Y k))) := by
  have hex (k : ℕ) := UnboundedGlobalHeatContinuity.exists_closed_version F
    (field (U k) (hG k) hβ hβ1) (predictable F (U k) (hU k) (hG k) hβ hβ1)
    (projection_holder B) (by norm_num) (by norm_num) μ H
    (Filter.Eventually.of_forall (norm_bound (U k) (hG k) hβ hβ1 B (hb k))) (P k) e
  choose Y hYm hYe hYc hYzero using hex
  let Z (k : ℕ) (sample : Ω) : C(Parameter, ℝ) := ⟨fun p ↦ Y k p sample, hYc k sample⟩
  have hZm (k : ℕ) : Measurable (Z k) :=
    ContinuousMap.measurable_iff_eval.mpr (hYm k)
  have hZe (k : ℕ) (p : Parameter) : (fun sample ↦ Z k sample p) =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto (P k).toCoordinates e).integral
        (GlobalBoundedHeatCoefficientLift.input F (U k) (hU k) (hG k) hβ hβ1 B (hb k) μ H (GlobalHeatParameter.time H p)
          (GlobalHeatParameter.time_le_horizon H p) (center p)) := hYe k p
  refine ⟨Z, hZm, hZe, ?_⟩
  let p₀ : Parameter := ⟨0, by simp [HeatParameterCover.region]⟩
  let M : ℝ≥0 := (GlobalBoundedHeatCoefficientLift.momentConstant (V := V) B H).toNNReal
  have hM : (M : ℝ≥0∞) = GlobalBoundedHeatCoefficientLift.momentConstant (V := V) B H :=
    ENNReal.coe_toNNReal (GlobalBoundedHeatCoefficientLift.momentConstant_finite (V := V) B H).ne
  apply KolmogorovFieldTightness.tight (fun _ : ℕ ↦ μ) Z hZm (zeroTime p₀)
    (fun k ↦ (hYzero k).mono fun sample hs ↦ hs.1 p₀)
    parameter_cover (by norm_num) (by norm_num : (0 : ℝ) < 2)
    (p := 64) (q := 4) (M := M) (α := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro k
  apply BDGKolmogorov.of_nat_moments μ (fun p sample ↦ Z k sample p)
    (fun p ↦ (ContinuousMap.measurable_eval p).comp (hZm k))
    64 (by norm_num) 4 (by norm_num) M
  intro p q
  calc
    _ = ∫⁻ sample, ENNReal.ofReal (‖
        (FiniteCylindricalIto.terminalIto (P k).toCoordinates e).integral
          (GlobalBoundedHeatCoefficientLift.input F (U k) (hU k) (hG k) hβ hβ1 B (hb k) μ H (GlobalHeatParameter.time H p)
            (GlobalHeatParameter.time_le_horizon H p) (center p)) sample -
        (FiniteCylindricalIto.terminalIto (P k).toCoordinates e).integral
          (GlobalBoundedHeatCoefficientLift.input F (U k) (hU k) (hG k) hβ hβ1 B (hb k) μ H (GlobalHeatParameter.time H q)
            (GlobalHeatParameter.time_le_horizon H q) (center q)) sample‖ ^ 64) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hZe k p, hZe k q] with sample hp hq
      rw [hp, hq]
    _ ≤ GlobalBoundedHeatCoefficientLift.momentConstant (V := V) B H * edist p q ^ (4 : ℝ) :=
      GlobalBoundedHeatCoefficientLift.native_moment F (U k) (hU k) (hG k) hβ hβ1 B (hb k) μ H (P k) e p q
    _ = _ := by rw [hM]

end SHEStochastic.GlobalBoundedHeatTightness
