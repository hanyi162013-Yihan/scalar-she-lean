module

public import SHEStochastic.ScalarLipschitzIntegratedComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzEnergyInputs
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzDampedEnergy ScalarLipschitzKernelBounds ScalarLipschitzConvolution
  ScalarLipschitzItoMoment ScalarLipschitzEnergyComparison ScalarLipschitzRawBounds
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
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))

local instance : MeasurableSpace (HilbertColumns.Space I RealL2) := borel _
local instance : BorelSpace (HilbertColumns.Space I RealL2) := ⟨rfl⟩

include hU in
/-- Integrated state energy suffices for the actual Hilbert input at
almost every terminal time. It is obtained by exchanging the finite
heat-age and state integrals. -/
theorem raw_ae_integrable
    (hM : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) :
    ∀ᵐ t ∂tm H,Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H) := by
  let η := energyMeasure μ H
  let _ : IsFiniteMeasure η := by dsimp only [η,energyMeasure]; infer_instance
  let a := fun p : ℝ≥0×Ω => timeWeight 1 p.1*coeffSquare hg U p
  let D := fun s : ℝ≥0 => ∫⁻ ω,a (s,ω) ∂μ
  let R := fun t : ℝ≥0 => ∫⁻ p,ENNReal.ofReal (‖raw e hg U t p‖^2) ∂η
  let K := ENNReal.ofReal (heatConstant (H : ℝ))
  have ha : Measurable a := ((timeWeight_measurable 1).comp measurable_fst).mul
    (coeffSquare_measurable hg U hU)
  have hD : Measurable D := ha.lintegral_prod_right'
  have hI : (∫⁻ s,D s ∂tm H)<⊤ := by
    rw [show (∫⁻ s,D s ∂tm H)=∫⁻ p,a p ∂η from (lintegral_prod _ ha.aemeasurable).symm]
    have hK := growth_nonneg g C
    have hf : Integrable (fun p : ℝ≥0×Ω => growth g C*(1+‖U p.1 p.2‖^2)) η :=
      ((integrable_const (1 : ℝ)).add hM).const_mul _
    refine (lintegral_mono (fun p => ?_)).trans_lt
      ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun p => by positivity))).mp hf.hasFiniteIntegral)
    change a p≤ENNReal.ofReal (growth g C*(1+‖U p.1 p.2‖^2))
    calc
      _ ≤ coeffSquare hg U p := by
        dsimp only [a]
        simpa only [one_mul] using mul_le_mul_left (timeWeight_le_one zero_le_one p.1) (coeffSquare hg U p)
      _ ≤ _ := ENNReal.ofReal_le_ofReal (coefficient_sq hg (U p.1 p.2))
  have hb (t : ℝ≥0) (ht : t≤H) :
      timeWeight 1 t*R t≤K*(∫⁻ s,BieleckiKernel.kernel H 1 ((t : ℝ)-(s : ℝ))*D s ∂tm t) := by
    let k := fun s : ℝ≥0 => BieleckiKernel.kernel H 1 ((t : ℝ)-(s : ℝ))
    have hk : Measurable k := (BieleckiKernel.measurable H 1).comp
      (measurable_const.sub NNReal.continuous_coe.measurable)
    have hRD : Measurable (fun p : ℝ≥0×Ω => ENNReal.ofReal (‖raw e hg U t p‖^2)) :=
      ((raw_measurable e hg U hU t).norm.pow_const (2 : ℕ)).ennreal_ofReal
    have hka : Measurable (fun p : ℝ≥0×Ω => (K*k p.1)*a p) :=
      (measurable_const.mul (hk.comp measurable_fst)).mul ha
    have hkD : Measurable (fun s => k s*D s) := hk.mul hD
    dsimp only [R]
    rw [←lintegral_const_mul'' (timeWeight 1 t) hRD.aemeasurable,←kernel_integral_support 1 ht D]
    calc
      _ ≤ ∫⁻ p,(K*k p.1)*a p ∂η := lintegral_mono (fun p => raw_growth e hg ht 1 U p)
      _ = _ := by
        rw [show η=(tm H).prod μ from rfl,lintegral_prod _ hka.aemeasurable,
          ←lintegral_const_mul'' K hkD.aemeasurable]
        apply lintegral_congr
        intro s
        have hsec : Measurable (fun ω => a (s,ω)) := ha.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_const_mul'' (K*k s) hsec.aemeasurable,mul_assoc]
  let L := fun t : ℝ≥0 => ∫⁻ s,BieleckiKernel.kernel H 1 ((t : ℝ)-(s : ℝ))*D s ∂tm H
  have hL : Measurable L := by
    have h : Measurable (fun p : ℝ≥0×ℝ≥0 => BieleckiKernel.kernel H 1 ((p.1 : ℝ)-(p.2 : ℝ))*D p.2) :=
      ((BieleckiKernel.measurable H 1).comp (by fun_prop)).mul (hD.comp measurable_snd)
    exact h.lintegral_prod_right'
  have hEq : ∀ᵐ t : ℝ≥0 ∂tm H,
      L t=∫⁻ s,BieleckiKernel.kernel H 1 ((t : ℝ)-(s : ℝ))*D s ∂tm t :=
    (timeMeasure_ae_mem H).mono (fun t ht => kernel_integral_support 1 ht.2 D)
  have hLfin : (∫⁻ t,L t ∂tm H)<⊤ := by
    rw [lintegral_congr_ae hEq]
    exact (BieleckiColumnEnergy.causal_energy H zero_lt_one D hD).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)
  filter_upwards [ae_lt_top hL hLfin.ne,timeMeasure_ae_mem H,hEq] with t ht htime hEq
  have ht' : timeWeight 1 t*R t<⊤ := by
    apply (hb t htime.2).trans_lt
    rw [←hEq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ht
  refine ⟨((raw_measurable e hg U hU t).stronglyMeasurable.norm.pow 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mpr ?_⟩
  change R t<⊤
  by_contra hn
  have he : R t=⊤ := top_le_iff.mp (le_of_not_gt hn)
  rw [he,ENNReal.mul_top (timeWeight_ne_zero 1 t)] at ht'
  exact (lt_irrefl ⊤) ht'

end SHEStochastic.ScalarLipschitzEnergyInputs
