module

public import SHEStochastic.ScalarLipschitzDampedEnergy
public import SHEStochastic.HolderWeightedEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzEnergyComparison
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzDampedEnergy ScalarLipschitzKernelBounds ScalarLipschitzConvolution ScalarLipschitzItoMoment
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

local instance : MeasurableSpace (HilbertColumns.Space I RealL2) := borel _
local instance : BorelSpace (HilbertColumns.Space I RealL2) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U V : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
  (hV : StronglyMeasurable[F.predictable] (Function.uncurry V))

def stateEnergy (μ : Measure Ω) (γ : ℝ) (U V : ℝ≥0 → Ω → RealL2) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω,timeWeight γ t*ENNReal.ofReal (‖U t ω-V t ω‖^2) ∂μ

theorem stateEnergy_measurable (γ : ℝ) (hUm : Measurable (Function.uncurry U))
    (hVm : Measurable (Function.uncurry V)) : Measurable (stateEnergy μ γ U V) :=
  (((timeWeight_measurable γ).comp measurable_fst).mul
    ((hUm.sub hVm).norm.pow_const (2 : ℕ)).ennreal_ofReal).lintegral_prod_right'

omit [IsProbabilityMeasure μ] in
theorem stateEnergy_factor (γ : ℝ) (t : ℝ≥0) (hUt : Measurable (U t)) (hVt : Measurable (V t)) :
    stateEnergy μ γ U V t = timeWeight γ t*moment 2 (fun ω => U t ω-V t ω) μ :=
  lintegral_const_mul'' _ (((hUt.sub hVt).norm.pow_const (2 : ℕ)).ennreal_ofReal.aemeasurable)

theorem kernel_integral_support (γ : ℝ) {t : ℝ≥0} (ht : t≤H) (D : ℝ≥0 → ℝ≥0∞) :
    (∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm H)=
      ∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*D s ∂tm t := by
  apply causal_lintegral_of_zero ht
  intro s hs
  rw [damped_zero γ hs.le,zero_mul]

theorem difference_bound (γ : ℝ) (t : ℝ≥0) (ht : t≤H)
    (hEU : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H))
    (hEV : Integrable (fun p => ‖raw e hg V t p‖^2) (energyMeasure μ H)) :
    timeWeight γ t*ENNReal.ofReal (‖(ito e P).integral (input e hg U hU t hEU)-
      (ito e P).integral (input e hg V hV t hEV)‖^2)≤
      ENNReal.ofReal (heatConstant (H : ℝ)*(C : ℝ)^2)*
        (∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*stateEnergy μ γ U V s ∂tm H) := by
  let a := input e hg U hU t hEU
  let b := input e hg V hV t hEV
  let k (s : ℝ≥0) := BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))
  let B := ENNReal.ofReal (heatConstant (H : ℝ)*(C : ℝ)^2)
  have hA : ∀ᵐ p ∂energyMeasure μ H,
      timeWeight γ t*ENNReal.ofReal (‖a p-b p‖^2)≤
        B*k p.1*(timeWeight γ p.1*ENNReal.ofReal (‖U p.1 p.2-V p.1 p.2‖^2)) := by
    filter_upwards [input_ae e hg U hU t hEU,input_ae e hg V hV t hEV] with p ha hb
    rw [ha,hb]
    exact raw_difference e hg ht γ U V p
  have hma := ((Lp.stronglyMeasurable a).mono (predictable_le_product F)).measurable
  have hmb := ((Lp.stronglyMeasurable b).mono (predictable_le_product F)).measurable
  have hm : Measurable (fun p : ℝ≥0×Ω => ENNReal.ofReal (‖a p-b p‖^2)) :=
    ((hma.sub hmb).norm.pow_const (2 : ℕ)).ennreal_ofReal
  have hU' := (hU.mono (predictable_le_product F)).measurable
  have hV' := (hV.mono (predictable_le_product F)).measurable
  have hD : Measurable (fun p : ℝ≥0×Ω =>
      timeWeight γ p.1*ENNReal.ofReal (‖U p.1 p.2-V p.1 p.2‖^2)) :=
    ((timeWeight_measurable γ).comp measurable_fst).mul
      ((hU'.sub hV').norm.pow_const (2 : ℕ)).ennreal_ofReal
  rw [(ito e P).difference_energy]
  calc
    _ = ∫⁻ s,∫⁻ ω,timeWeight γ t*ENNReal.ofReal (‖a (s,ω)-b (s,ω)‖^2) ∂μ ∂tm H := by
      rw [←lintegral_const_mul'' (timeWeight γ t) hm.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro s
      exact (lintegral_const_mul'' (timeWeight γ t)
        (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    _ ≤ ∫⁻ s,∫⁻ ω,B*k s*(timeWeight γ s*ENNReal.ofReal (‖U s ω-V s ω‖^2)) ∂μ ∂tm H := by
      apply lintegral_mono_ae
      filter_upwards [Measure.ae_ae_of_ae_prod hA] with s hs
      exact lintegral_mono_ae hs
    _ = _ := by
      have hk : Measurable k := (BieleckiKernel.measurable H γ).comp
        (measurable_const.sub NNReal.continuous_coe.measurable)
      change _ = B*(∫⁻ s,k s*stateEnergy μ γ U V s ∂tm H)
      have hkD : Measurable (fun s => k s*stateEnergy μ γ U V s) :=
        hk.mul (stateEnergy_measurable U V γ hU' hV')
      rw [←lintegral_const_mul'' B hkD.aemeasurable]
      apply lintegral_congr
      intro s
      rw [←mul_assoc]
      exact lintegral_const_mul'' (B*k s)
        (hD.comp (measurable_const.prodMk measurable_id)).aemeasurable

theorem difference_sup {γ : ℝ} (hγ : 0<γ) (t : ℝ≥0) (ht : t≤H)
    (hEU : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H))
    (hEV : Integrable (fun p => ‖raw e hg V t p‖^2) (energyMeasure μ H))
    (D : ℝ≥0∞) (hD : ∀ᵐ s ∂tm H,stateEnergy μ γ U V s≤D) :
    timeWeight γ t*ENNReal.ofReal (‖(ito e P).integral (input e hg U hU t hEU)-
      (ito e P).integral (input e hg V hV t hEV)‖^2)≤
      ENNReal.ofReal (heatConstant (H : ℝ)*(C : ℝ)^2*BieleckiKernel.mass γ)*D := by
  let k (s : ℝ≥0) := BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))
  have hk : Measurable k := (BieleckiKernel.measurable H γ).comp
    (measurable_const.sub NNReal.continuous_coe.measurable)
  have hI :
      (∫⁻ s,k s*stateEnergy μ γ U V s ∂tm H)≤ENNReal.ofReal (BieleckiKernel.mass γ)*D := by
    calc
      _ ≤ ∫⁻ s,k s*D ∂tm H := lintegral_mono_ae (hD.mono (fun s h => mul_le_mul_right h _))
      _ = (∫⁻ s,k s ∂tm H)*D := lintegral_mul_const'' D hk.aemeasurable
      _ ≤ _ := mul_le_mul_left (ScalarLipschitzWeightedMoment.damped_mass H hγ ht) _
  refine (difference_bound e P hg U V hU hV γ t ht hEU hEV).trans ?_
  have hA : 0≤heatConstant (H : ℝ)*(C : ℝ)^2 :=
    mul_nonneg (heatConstant_nonneg H.property) (sq_nonneg (C : ℝ))
  rw [ENNReal.ofReal_mul (q := BieleckiKernel.mass γ) hA,mul_assoc]
  exact mul_le_mul_right hI _

end SHEStochastic.ScalarLipschitzEnergyComparison
