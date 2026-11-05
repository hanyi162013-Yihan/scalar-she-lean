module

public import SHEStochastic.SmoothMildRestart
public import SHEStochastic.RealHaarSemigroup
public import SHE.HilbertItoNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.SmoothMildSegment
open MeasureTheory SHE SHE.PredictableL2 SHE.LowBands SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0)
  (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) F μ H)
  {a : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ} (hell : 0 < ell)
  (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap) (Z : Ω → StateL2)

def kernel (U : ℝ≥0 → Ω → StateL2) (t : ℝ≥0) (p : ℝ≥0 × Ω) : RealHaarIntegrand.Columns :=
  RealHaarIntegrand.kernel ell cap hell
    ((t : ℝ)-(p.1 : ℝ), ContinuousHeatMild.coefficientFunction ha hell hb U p)

theorem kernel_eq_damped (U : ℝ≥0 → Ω → StateL2) (t : ℝ≥0) :
    kernel ha hell hb U t = DampedFixedIntegral.kernel (Λ := 0) hell
      (ContinuousHeatMild.coefficientFunction ha hell hb U) t := by
  funext p
  simp only [kernel, DampedFixedIntegral.kernel, DampedHeatKernel.kernel,
    neg_zero, zero_mul, Real.exp_zero, one_smul]

/-- A continuous adapted mild segment represented by inputs of ONE
fixed global integral. Its horizon may be shorter than that integral's
horizon, making deterministic restart and semigroup propagation literal. -/
structure Data (K : ℝ≥0) where
  value : ℝ≥0 → Ω → StateL2
  continuous : ∀ ω, Continuous (value · ω)
  predictable : StronglyMeasurable[F.predictable] (Function.uncurry value)
  input : (t : ℝ≥0) → t ≤ K → Process (E := RealHaarIntegrand.Columns) F μ H
  input_ae : ∀ t ht, input t ht =ᵐ[energyMeasure μ H] kernel ha hell hb value t
  equation : ∀ t ht, value t =ᵐ[μ] fun ω ↦ RealHeat.realHeat (t : ℝ) (Z ω)+I.integral (input t ht) ω

variable {F μ H I ha hell hb Z}

/-- Every reached deterministic state retains the square integrability
needed to restart the same Picard construction. -/
theorem memLp {K : ℝ≥0} (D : Data F μ H I ha hell hb Z K)
    (hZ : MemLp Z 2 μ) (t : ℝ≥0) (ht : t ≤ K) : MemLp (D.value t) 2 μ := by
  have hh : MemLp (fun ω ↦ RealHeat.realHeat (t : ℝ) (Z ω)) 2 μ :=
    hZ.mono ((RealHeat.realHeat (t : ℝ)).continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ RealHeat.realHeat_contraction _ _)
  exact (memLp_congr_ae (D.equation t ht)).mpr (hh.add (Lp.memLp (I.integral (D.input t ht))))

/-- The zero-length initial segment uses the same initial data and the
zero global input; it needs no positive-time construction. -/
def zero (hZ : StronglyMeasurable[F 0] Z) : Data F μ H I ha hell hb Z 0 where
  value := fun _ ↦ Z
  continuous := fun _ ↦ continuous_const
  predictable := ContinuousPredictable.stronglyMeasurable F (fun _ ↦ Z)
    (fun t ↦ hZ.mono (F.mono bot_le)) (fun _ ↦ continuous_const)
  input := fun _ _ ↦ 0
  input_ae := by
    intro t ht
    have hz : t = 0 := le_antisymm ht zero_le
    subst t
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_zero RealHaarIntegrand.Columns 2
      ((energyMeasure μ H).trim (predictable_le_product F)))] with p hp
    rw [hp]
    exact (HaarKernelApproximation.kernel_zero hell
      (by simp only [NNReal.coe_zero, zero_sub]; exact neg_nonpos.mpr p.1.2) _).symm
  equation := by
    intro t ht
    have hz : t = 0 := le_antisymm ht zero_le
    subst t
    filter_upwards [Lp.coeFn_zero StateL2 2 μ] with ω hω
    simp only [NNReal.coe_zero, RealHeat.realHeat_zero, ContinuousLinearMap.id_apply, map_zero, hω, Pi.zero_apply, add_zero]

end SHEStochastic.SmoothMildSegment
