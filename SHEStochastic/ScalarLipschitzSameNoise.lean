module

public import SHEStochastic.ScalarLipschitzEnergyInputs
public import SHEStochastic.ScalarLipschitzZeroEquation
public import SHEStochastic.ScalarLipschitzMomentBall
public import SHE.NativePathLawComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzSameNoise
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzDampedEnergy ScalarLipschitzKernelBounds ScalarLipschitzConvolution
  ScalarLipschitzEnergyComparison ScalarLipschitzIntegratedComparison ScalarLipschitzMomentBall
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "haar" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 haar
local notation "tm" => PredictableL2.timeMeasure
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance (h : ℝ≥0) : MeasurableSpace (Lp RealL2 2 (SHE.timeMeasure (h : ℝ))) := borel _
local instance (h : ℝ≥0) : BorelSpace (Lp RealL2 2 (SHE.timeMeasure (h : ℝ))) := ⟨rfl⟩

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U V : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
  (hV : StronglyMeasurable[F.predictable] (Function.uncurry V))
  (hEU : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H))
  (hEV : Integrable (fun p : ℝ≥0×Ω => ‖V p.1 p.2‖^2) (energyMeasure μ H))
  (u₀ : RealL2)
  (hEqU : ScalarLipschitzZeroEquation.Equation e P hg U hU hEU u₀)
  (hEqV : ScalarLipschitzZeroEquation.Equation e P hg V hV hEV u₀)

include hEqU hEqV in
/-- Shared-noise uniqueness only uses the derived integrated state
moment of a weak solution. In particular no high-moment bound on a
competing solution is imposed. -/
theorem ae_eq : Function.uncurry U=ᵐ[energyMeasure μ H] Function.uncurry V := by
  let A := heatConstant (H : ℝ)*(C : ℝ)^2
  have hA : 0≤A := mul_nonneg (heatConstant_nonneg H.property) (sq_nonneg (C : ℝ))
  obtain ⟨γ,hγ,hsmall⟩ := BieleckiKernel.exists_contraction_weight A
  have hγ' : 0<γ := zero_lt_one.trans_le hγ
  have hX := (hU.mono (predictable_le_product F)).measurable
  have hY := (hV.mono (predictable_le_product F)).measurable
  have h := ScalarLipschitzIntegratedComparison.integrated e P hg U V hU hV hγ' U V hX hY (by
    filter_upwards [timeMeasure_ae_mem H,
      ScalarLipschitzEnergyInputs.raw_ae_integrable e hg U hU hEU,
      ScalarLipschitzEnergyInputs.raw_ae_integrable e hg V hV hEV] with t ht hEt hEt'
    refine ⟨hEt,hEt',?_⟩
    filter_upwards [ScalarLipschitzZeroEquation.mild e P hg U hU hEU u₀ hEqU t ht.2 hEt,
      ScalarLipschitzZeroEquation.mild e P hg V hV hEV u₀ hEqV t ht.2 hEt'] with ω h₁ h₂
    rw [h₁,h₂,add_sub_add_left_eq_sub])
  let a := processOf U hU hEU
  let b := processOf V hV hEV
  let w := PredictableExponential.scale F μ H (-γ) (a-b)
  have hW : a-b =ᵐ[energyMeasure μ H] fun p => U p.1 p.2-V p.1 p.2 := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub a b),processOf_ae U hU hEU,
      processOf_ae V hV hEV] with p h₁ h₂ h₃
    rw [h₁,Pi.sub_apply]
    exact congrArg₂ HSub.hSub h₂ h₃
  rw [←class_energy γ (a-b) U V hW] at h
  have hB := mul_nonneg hA (BieleckiKernel.mass_nonneg hγ'.le)
  change ENNReal.ofReal (‖w‖^2)≤ENNReal.ofReal (A*BieleckiKernel.mass γ)*ENNReal.ofReal (‖w‖^2) at h
  rw [←ENNReal.ofReal_mul hB] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (sq_nonneg ‖w‖))).mp h
  have hw : w=0 := norm_eq_zero.mp (by
    nlinarith only [hr,mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖w‖),norm_nonneg w])
  have hzero : a-b=0 := by
    have he := congrArg (PredictableExponential.scale F μ H γ) hw
    change PredictableExponential.scale F μ H γ (PredictableExponential.scale F μ H (-γ) (a-b)) =
      PredictableExponential.scale F μ H γ 0 at he
    rw [PredictableExponential.cancel'] at he
    have hz : PredictableExponential.scale F μ H γ (0 : Process (E := RealL2) F μ H)=0 := by
      have h : PredictableExponential.scale F μ H γ ((0 : Process (E := RealL2) F μ H)-0)=0 := by
        rw [PredictableExponential.sub,sub_self]
      simpa only [sub_self] using h
    exact he.trans hz
  have hab := sub_eq_zero.mp hzero
  have ha : a=ᵐ[energyMeasure μ H] Function.uncurry U := processOf_ae U hU hEU
  have hb : b=ᵐ[energyMeasure μ H] Function.uncurry V := processOf_ae V hV hEV
  rw [←hab] at hb
  exact ha.symm.trans hb

include hEqU hEqV in
theorem laws_eq (hH : 0<H) (hcU : ∀ ω,Continuous (fun t => U t ω))
    (hcV : ∀ ω,Continuous (fun t => V t ω)) :
    μ.map (NativeContinuousPath.path H U hcU)=μ.map (NativeContinuousPath.path H V hcV) := by
  have he := ae_eq e P hg U V hU hV hEU hEV u₀ hEqU hEqV
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := tm H)).quasiMeasurePreserving.ae he
  have hi : NativeContinuousPath.integrated H U hcU =ᵐ[μ] NativeContinuousPath.integrated H V hcV := by
    filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have h := NativeContinuousPath.difference_norm_sq H U hcU V hcV ω
    rw [integral_congr_ae (show (fun t => ‖U t ω-V t ω‖^2)=ᵐ[tm H] fun _ => 0 from
      hω.mono (fun t ht => by
        change U t ω=V t ω at ht
        change ‖U t ω-V t ω‖^2=0
        rw [ht,sub_self,norm_zero]
        norm_num)),
      integral_zero] at h
    exact (pow_eq_zero_iff (by decide : (2 : ℕ)≠0)).mp h
  have h₁ := NativePathLawComparison.integrated_law H μ U hcU
    (hU.mono (predictable_le_product F)).measurable
  have h₂ := NativePathLawComparison.integrated_law H μ V hcV
    (hV.mono (predictable_le_product F)).measurable
  have hMap := Measure.map_congr (mβ := borel (Lp RealL2 2 (SHE.timeMeasure (H : ℝ)))) hi
  have hLaw : NativePathLawComparison.law H μ U hcU=NativePathLawComparison.law H μ V hcV := by
    apply SHE.interval_path_laws_eq_of_integrated_laws (by exact_mod_cast hH)
    rw [h₁,h₂]
    exact Subtype.ext hMap
  exact congrArg Subtype.val hLaw

end SHEStochastic.ScalarLipschitzSameNoise
