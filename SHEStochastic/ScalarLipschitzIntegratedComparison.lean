module

public import SHEStochastic.ScalarLipschitzEnergyComparison
public import SHE.PredictableExponential

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzIntegratedComparison
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzDampedEnergy ScalarLipschitzKernelBounds ScalarLipschitzConvolution
  ScalarLipschitzItoMoment ScalarLipschitzEnergyComparison
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "tm" => PredictableL2.timeMeasure
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U V : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
  (hV : StronglyMeasurable[F.predictable] (Function.uncurry V))

/-- Integrate the literal difference of two stochastic convolutions
after weighting both time variables. This uses the same noise. -/
theorem integrated {γ : ℝ} (hγ : 0<γ) (X Y : ℝ≥0 → Ω → RealL2)
    (hX : Measurable (Function.uncurry X)) (hY : Measurable (Function.uncurry Y))
    (hFix : ∀ᵐ t ∂tm H, ∃ (hEU : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H))
      (hEV : Integrable (fun p => ‖raw e hg V t p‖^2) (energyMeasure μ H)),
      (fun ω => X t ω-Y t ω)=ᵐ[μ] fun ω =>
        (ito e P).integral (input e hg U hU t hEU) ω-
          (ito e P).integral (input e hg V hV t hEV) ω) :
    (∫⁻ t,stateEnergy μ γ X Y t ∂tm H)≤
      ENNReal.ofReal (heatConstant (H : ℝ)*(C : ℝ)^2*BieleckiKernel.mass γ)*
        (∫⁻ t,stateEnergy μ γ U V t ∂tm H) := by
  let B := ENNReal.ofReal (heatConstant (H : ℝ)*(C : ℝ)^2)
  let D := stateEnergy μ γ U V
  have hD : Measurable D := stateEnergy_measurable U V γ
    (hU.mono (predictable_le_product F)).measurable (hV.mono (predictable_le_product F)).measurable
  have hB (t : ℝ≥0) (ht : t≤H) (hEU : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H))
      (hEV : Integrable (fun p => ‖raw e hg V t p‖^2) (energyMeasure μ H))
      (hEq : (fun ω => X t ω-Y t ω)=ᵐ[μ] fun ω =>
        (ito e P).integral (input e hg U hU t hEU) ω-
          (ito e P).integral (input e hg V hV t hEV) ω) :
      stateEnergy μ γ X Y t≤B*(∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm t) := by
    have hXt : Measurable (X t) := hX.comp (measurable_const.prodMk measurable_id)
    have hYt : Measurable (Y t) := hY.comp (measurable_const.prodMk measurable_id)
    let a := (ito e P).integral (input e hg U hU t hEU)
    let b := (ito e P).integral (input e hg V hV t hEV)
    rw [stateEnergy_factor X Y γ t hXt hYt,moment_congr (hEq.trans (Lp.coeFn_sub a b).symm)]
    change timeWeight γ t*moment 2 (a-b : Lp RealL2 2 μ) μ≤_
    rw [moment,HolderWeightedEnergy.state_mass]
    rw [←kernel_integral_support γ ht D]
    exact difference_bound e P hg U V hU hV γ t ht hEU hEV
  have hm :
      Measurable (fun t : ℝ≥0 => ∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm H) := by
    have h : Measurable (fun p : ℝ≥0×ℝ≥0 => BieleckiKernel.kernel H γ ((p.1 : ℝ)-(p.2 : ℝ))*D p.2) :=
      ((BieleckiKernel.measurable H γ).comp (by fun_prop)).mul (hD.comp measurable_snd)
    exact h.lintegral_prod_right'
  calc
    _ ≤ ∫⁻ t,B*(∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm t) ∂tm H := by
      apply lintegral_mono_ae
      filter_upwards [hFix,timeMeasure_ae_mem H] with t ⟨hEU,hEV,he⟩ ht
      exact hB t ht.2 hEU hEV he
    _ = B*(∫⁻ t,∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm t ∂tm H) := by
      have he : ∀ᵐ (t : ℝ≥0) ∂tm H,
          (∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm H) =
            ∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm t :=
        (timeMeasure_ae_mem H).mono (fun t ht => kernel_integral_support γ ht.2 D)
      calc
        _ = ∫⁻ t,B*(∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm H) ∂tm H :=
          lintegral_congr_ae (he.mono (fun _ h => congrArg (fun z => B*z) h.symm))
        _ = _ := by rw [lintegral_const_mul'' B hm.aemeasurable,lintegral_congr_ae he]
    _ ≤ _ := by
      have hA : 0≤heatConstant (H : ℝ)*(C : ℝ)^2 :=
        mul_nonneg (heatConstant_nonneg H.property) (sq_nonneg (C : ℝ))
      rw [ENNReal.ofReal_mul (q := BieleckiKernel.mass γ) hA,mul_assoc]
      exact mul_le_mul_right (BieleckiColumnEnergy.causal_energy H hγ D hD) B

/-- Ambient representatives of the scaled predictable class have the
same integrated weighted energy as the actual process pair. -/
theorem class_energy (γ : ℝ) (v : Process (E := RealL2) F μ H)
    (X Y : ℝ≥0 → Ω → RealL2)
    (hv : v=ᵐ[energyMeasure μ H] (fun p => X p.1 p.2-Y p.1 p.2)) :
    ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ) v‖^2)=
      ∫⁻ t,stateEnergy μ γ X Y t ∂tm H := by
  rw [PredictableExponential.energy]
  unfold stateEnergy
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hv] with t ht
  apply lintegral_congr_ae
  filter_upwards [ht] with ω hω
  rw [hω]
  rw [timeWeight,←ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [show (2 : ℝ)*(-γ)*(t : ℝ)=(-2)*γ*(t : ℝ) by ring]

end SHEStochastic.ScalarLipschitzIntegratedComparison
