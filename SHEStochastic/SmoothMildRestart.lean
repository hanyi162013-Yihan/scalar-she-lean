module

public import SHEStochastic.SmoothRandomMildExistence
public import SHE.DeterministicItoShiftBDG
public import SHEStochastic.AdaptedRestartGluing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.SmoothMildRestart
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
  (H v h : ℝ≥0) (hvh : v+h ≤ H)
  (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) F μ H)
  (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)

local notation "FV" => SHE.DeterministicItoShift.filtration F v

include hBDG in
/-- Restart the existing Picard construction on a deterministic window,
using the SAME global integral through literal input extension. -/
theorem exists_window (hh : (h : ℝ) ≤ 1) (hp : 0 < h)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    {a : ℝ → ℝ} (ha : Measurable a) {ell cap K β : ℝ}
    (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
    (hβ : 0 < β) (hK : 0 ≤ K) (hholder : ∀ z w, |a z-a w| ≤ K*|z-w|^β)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z ↦ (a z : ℂ)))
    (Z : Ω → StateL2) (hZ₀ : StronglyMeasurable[F v] Z) (hZ : MemLp Z 2 μ) :
    ∃ U : ℝ≥0 → Ω → StateL2, (∀ ω, Continuous (U · ω)) ∧
      StronglyMeasurable[(FV).predictable] (Function.uncurry U) ∧
      ∃ hf : StronglyMeasurable[(FV).predictable] (ContinuousHeatMild.coefficientFunction ha hell hb U),
      ∀ (t : ℝ≥0) (ht : t ≤ h), U t =ᵐ[μ] fun ω ↦ RealHeat.realHeat (t : ℝ) (Z ω) +
        I.integral (SHE.DeterministicItoShift.input F μ H v h hvh
          (DampedFixedIntegral.input FV μ h hh (Λ := 0) (by norm_num) hell
            (hell.le.trans ((hb 0).1.trans (hb 0).2))
            (ContinuousHeatMild.coefficientFunction ha hell hb U) hf t ht)) ω := by
  have hn : NullCompleteFiltration.ContainsNullSets FV μ := fun t A hA ↦ hnull (v+t) A hA
  have hz : StronglyMeasurable[FV 0] Z := by
    change StronglyMeasurable[F (v+0)] Z
    rw [add_zero]
    exact hZ₀
  exact SmoothRandomMildExistence.exists_mild FV μ h hh ha hell hb hβ hK hholder
    (SHE.DeterministicItoShift.integral F μ H v h hvh I) B
    (SHE.DeterministicItoShift.bdg16 F μ H v h hvh I B hBDG) hp hn hLip Z hz hZ

end SHEStochastic.SmoothMildRestart
