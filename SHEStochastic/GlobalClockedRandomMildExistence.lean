module

public import SHEStochastic.GlobalClockedMildSegment
public import SHEStochastic.NativeTimeDilatedFamily

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.GlobalClockedRandomMildExistence
open MeasureTheory SHE SHE.PredictableL2 SHE.LowBands SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ RealHaarInput)
  (b : HilbertBasis κ ℝ StateL2)

local notation "FN" => PredictableTimeDilation.filtration F
  (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)
local notation "I" => NativeSmoothRandomMildExistence.integral F μ H P e
  (LinearIsometry.id : RealHaarInput →ₗᵢ[ℝ] RealHaarInput) b

/-- Smooth random-initial native mild existence in the physical heat
clock on every finite horizon. Short-window Picard and deterministic
restarts construct all stochastic inputs from the same original noise. -/
theorem exists_mild (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    {a : ℝ → ℝ} (ha : Measurable a) {ell cap K β : ℝ}
    (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
    (hβ : 0 < β) (hK : 0 ≤ K) (hholder : ∀ z w, |a z-a w| ≤ K*|z-w|^β)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z ↦ (a z : ℂ)))
    (Z : Ω → StateL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ U : ℝ≥0 → Ω → StateL2, (∀ ω, Continuous (U · ω)) ∧
      StronglyMeasurable[(FN).predictable] (Function.uncurry U) ∧
      ∃ hf : StronglyMeasurable[(FN).predictable] (ContinuousHeatMild.coefficientFunction ha hell hb U),
      ∃ v : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) FN μ (NativeClock.rate*H),
        (∀ t, t ≤ NativeClock.rate*H → v t =ᵐ[energyMeasure μ (NativeClock.rate*H)] fun p ↦
          NativeHeatObservation.kernel ell cap hell
            ((t : ℝ)-(p.1 : ℝ), ContinuousHeatMild.coefficientFunction ha hell hb U p)) ∧
        ∀ t, t ≤ NativeClock.rate*H → U t =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat (t : ℝ) (Z ω) +
          (PredictableTimeDilation.integral F μ NativeClock.rate NativeClock.rate_pos H I).integral (v t) ω := by
  let c : ℝ := NativeClock.rate
  have hc : 0 < c := NativeClock.rate_pos
  have hh (z w : ℝ) : |c*a z-c*a w| ≤ (c*K)*|z-w|^β := by
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left (hholder z w) hc.le).trans_eq (mul_assoc _ _ _).symm
  have hL : LipschitzWith (‖c‖₊*L) (fun z ↦ ((c*a z : ℝ) : ℂ)) := by
    convert (lipschitzWith_smul c).comp hLip using 1
    funext z
    simp only [Function.comp_apply, Complex.real_smul, Complex.ofReal_mul]
  obtain ⟨D⟩ := AllHorizonSmoothMild.native (F := F) (μ := μ) (H := H) (hnull := hnull)
    (ha := ha.const_mul c) (hell := mul_pos hc hell) (hb := HaarFieldScaling.scaled_bounds hc hb)
    (hβ := hβ) (hK := mul_nonneg hc.le hK) (hholder := hh) (hLip := hL)
    (Z := Z) (hZ₀ := hZ₀) (hZ := hZ) P e b
  let hm := NonlinearHaarIntegrand.coefficientField_measurable ha hell hb hβ hK hholder
  refine ⟨GlobalClockedMildSegment.path F μ H I ha hell hb Z D,
    ClockedPairFields.path_continuous NativeClock.rate NativeClock.rate_pos D.value D.continuous,
    ClockedPairFields.path_predictable F NativeClock.rate NativeClock.rate_pos D.value D.predictable,
    ClockedPairFields.coefficient_predictable F NativeClock.rate NativeClock.rate_pos ha hell hb hm D.value D.predictable,
    GlobalClockedMildSegment.input F μ H I ha hell hb Z D, ?_, ?_⟩
  · exact GlobalClockedMildSegment.input_ae F μ H I ha hell hb Z D
  · exact GlobalClockedMildSegment.mild F μ H I ha hell hb Z D

end SHEStochastic.GlobalClockedRandomMildExistence
