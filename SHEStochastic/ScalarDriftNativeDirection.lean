module

public import SHEStochastic.ScalarLinearGrowthDriftField
public import SHEStochastic.NativePhysicalState
public import SHEStochastic.NativeEnergy
public import SHEStochastic.NativeRowRepresentatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarDriftNativeDirection
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.PredictableL2 AddCircle
open scoped ENNReal NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {H : ℝ≥0}
    (b : ScalarLinearGrowthDriftField.Data H) (U : ℝ≥0×Ω→RealL2)
    (hU : StronglyMeasurable[F.predictable] U)
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

/-- The noise direction in the native Hilbert space. Taking the Borel
field to be b/g gives the actual Girsanov control. -/
def row (p : ℝ≥0×Ω) : Noise :=
  NativePhysicalState.push (ScalarLinearGrowthDriftField.field b (p.1,U p))

include hU in
theorem predictable : StronglyMeasurable[F.predictable] (row b U) := by
  have ht : Measurable[F.predictable] (fun p : ℝ≥0×Ω => p.1) := by
    simpa only [Function.comp_def,Real.toNNReal_coe] using
      measurable_real_toNNReal.comp (PredictableClock.real_time_measurable F)
  exact NativePhysicalState.push.continuous.comp_stronglyMeasurable
    ((ScalarLinearGrowthDriftField.field_measurable b).comp (ht.prodMk hU.measurable)).stronglyMeasurable

omit [MeasurableSpace Ω] in
theorem row_norm_sq_le (p : ℝ≥0×Ω) :
    ‖row b U p‖^2≤2*(b.growth : ℝ)^2*(1+‖U p‖^2) := by
  unfold row
  rw [LinearIsometry.norm_map]
  exact ScalarLinearGrowthDriftField.field_norm_sq_le b (p.1,U p)

include hU in
theorem memLp (hM : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H)) :
    MemLp (row b U) 2 νin := by
  have hp := predictable F b U hU
  have hA : AEStronglyMeasurable (row b U) (energyMeasure μ H) :=
    (hp.mono (predictable_le_product F)).aestronglyMeasurable
  let : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  have hI : Integrable (fun p => ‖row b U p‖^2) (energyMeasure μ H) := by
    apply (((integrable_const (1 : ℝ)).add hM).const_mul (2*(b.growth : ℝ)^2)).mono'
      (hA.norm.pow 2) 
    apply ae_of_all _
    intro p
    change ‖‖row b U p‖^2‖≤2*(b.growth : ℝ)^2*(1+‖U p‖^2)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact row_norm_sq_le b U p
  have hL := (memLp_two_iff_integrable_sq_norm hA).mpr hI
  have htrim : MemLp (row b U) 2 ((energyMeasure μ H).trim (predictable_le_product F)) :=
    (eLpNorm_trim (predictable_le_product F) hp).trans_lt hL
  simpa only [NativeRowRepresentatives.inputMeasure_eq] using htrim

include hU in
/-- The actual predictable control and its terminal pathwise energy.
The same energy estimate is valid under every absolutely continuous
tilted law, since the time-fibre identity is retained there. -/
theorem exists_control (hM : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H)) :
    ∃ u : Lp Noise 2 νin, u =ᵐ[νin] row b U ∧
      ∀ (Q : Measure Ω),Q ≪ μ →
        (∫⁻ ω,ENNReal.ofReal (NativeEnergy.energy u ω) ∂Q) ≤
        ∫⁻ ω, (∫⁻ t,ENNReal.ofReal (2*(b.growth : ℝ)^2*(1+‖U (t,ω)‖^2)) ∂νt) ∂Q := by
  let h := memLp F μ b U hU hM
  let u := h.toLp (row b U)
  have hu : u =ᵐ[νin] row b U := h.coeFn_toLp
  refine ⟨u,hu,?_⟩
  intro Q hQ
  have hRep := ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) hu
  have hI : Integrable (fun p => ‖row b U p‖^2) ((νt).prod μ) :=
    (NativeEnergy.product_memLp u).norm.integrable_sq.congr
      (hRep.mono (fun _ hp => congrArg (fun z : Noise => ‖z‖^2) hp))
  apply lintegral_mono_ae
  filter_upwards [hQ.ae_eq (NativeEnergy.energy_ae_of_ae u _ hu),hQ.ae_le hI.prod_left_ae] with ω he hInt
  rw [he,ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (fun _ => sq_nonneg _))]
  exact lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (row_norm_sq_le b U (t,ω)))

end SHEStochastic.ScalarDriftNativeDirection
