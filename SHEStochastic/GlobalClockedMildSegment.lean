module

public import SHEStochastic.AllHorizonSmoothMild
public import SHE.ClockedPairFields
public import SHE.ClockedPairIntegral
public import SHE.NativeClock

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.GlobalClockedMildSegment
open MeasureTheory SHE SHE.PredictableL2 SHE.LowBands SHE.FiniteHaar SHE.PredictableTimeDilation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) F μ H)
  {a : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ} (hell : 0 < ell)
  (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap) (Z : Ω → StateL2)

local notation "c" => NativeClock.rate
local notation "hc" => NativeClock.rate_pos
local notation "FN" => filtration F (clock c hc)

variable (D : SmoothMildSegment.Data F μ H I (ha.const_mul (c : ℝ)) (mul_pos hc hell)
  (HaarFieldScaling.scaled_bounds hc hb) Z H)

def path : ℝ≥0 → Ω → StateL2 := ClockedPairFields.path c hc D.value

def input (t : ℝ≥0) : Process (E := RealHaarIntegrand.Columns) FN μ (c*H) :=
  if ht : t ≤ c*H then (processEquivalence F μ c hc H).symm
    (D.input (NativeClock.time t) (ClockedPairIntegral.time_le c hc H ht)) else 0

/-- The transported global input is the literal physical heat-Haar
kernel for the transported state, for every time in the full horizon. -/
theorem input_ae (t : ℝ≥0) (ht : t ≤ c*H) :
    input F μ H I ha hell hb Z D t =ᵐ[energyMeasure μ (c*H)] fun p ↦
      NativeHeatObservation.kernel ell cap hell ((t : ℝ)-(p.1 : ℝ),
        ContinuousHeatMild.coefficientFunction ha hell hb (path F μ H I ha hell hb Z D) p) := by
  rw [input, dif_pos ht]
  let u := D.input (NativeClock.time t) (ClockedPairIntegral.time_le c hc H ht)
  have hrev := ScaledLpPull.inverse_preserving (energyMeasure μ H) (energyMeasure μ (c*H))
    (c : ℝ) hc (ambientEquiv c hc) (energyMeasure_clock_preserving c hc H μ)
  have hu := hrev.quasiMeasurePreserving.ae (D.input_ae (NativeClock.time t) (ClockedPairIntegral.time_le c hc H ht))
  have hu' := (Measure.ae_ennreal_smul_measure_iff
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (show (0 : ℝ)<c from hc)))).mp hu
  filter_upwards [processEquivalence_symm_ae F μ c hc H u, hu'] with p hp hq
  change u ((clock c hc).symm p.1,p.2) = _ at hq
  rw [hp, hq]
  have hpair : (ambientEquiv c hc).symm p = ((clock c hc).symm p.1,p.2) := rfl
  rw [hpair]
  unfold SmoothMildSegment.kernel
  rw [← ClockedPairFields.unitField_coefficient c hc ha hell hb D.value]
  simp only [ClockedHaarIntegral.unitField, OrderIso.apply_symm_apply]
  have hs := ClockedHaarIntegral.scaled_kernel c hc hell (Λ := 0) (t := t) (s := p.1)
    (ContinuousHeatMild.coefficientFunction ha hell hb (path F μ H I ha hell hb Z D) p)
  simp only [DampedHeatKernel.kernel, neg_zero, zero_mul, mul_zero, Real.exp_zero, one_smul] at hs
  convert! hs using 1 <;> rfl

/-- The actual native physical-clock mild equation on the entire
finite horizon, with no artificial normalized-time upper bound. -/
theorem mild (t : ℝ≥0) (ht : t ≤ c*H) :
    path F μ H I ha hell hb Z D t =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat (t : ℝ) (Z ω) +
      (PredictableTimeDilation.integral F μ c hc H I).integral
        (input F μ H I ha hell hb Z D t) ω := by
  have he : (PredictableTimeDilation.integral F μ c hc H I).integral (input F μ H I ha hell hb Z D t) =
      I.integral (D.input (NativeClock.time t) (ClockedPairIntegral.time_le c hc H ht)) := by
    rw [input, dif_pos ht]
    exact PredictableTimeDilation.integral_push F μ c hc H I _
  filter_upwards [D.equation (NativeClock.time t) (ClockedPairIntegral.time_le c hc H ht)] with ω hs
  change D.value (NativeClock.time t) ω = _
  have hh := congrArg (fun L : StateL2 →L[ℝ] StateL2 ↦ L (Z ω)) (NativeClock.heat_time t)
  exact hs.trans (congrArg₂ (fun x y : StateL2 ↦ x+y) hh (congrArg (fun u : Lp StateL2 2 μ ↦ u ω) he).symm)

end SHEStochastic.GlobalClockedMildSegment
