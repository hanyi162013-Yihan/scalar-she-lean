module

public import SHEStochastic.NativeHilbertBDG
public import SHEStochastic.HilbertIntegralUniqueness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.DirectHilbertBDG
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω ι κ β E : Type*} [MeasurableSpace Ω] [Countable ι] [Countable κ]
  [Countable β] [DecidableEq β]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
local instance : MeasurableSpace (Space ι ℝ) := borel _
local instance : BorelSpace (Space ι ℝ) := ⟨rfl⟩

theorem integral_identity (J : StandardTerminalIto (C := Space ι ℝ) (E := ℝ) F μ H)
    (b : HilbertBasis κ ℝ E) (u : Process (E := Space ι E) F μ H) :
    (HilbertTerminalIto.terminalIto F μ H b (restrictNoise J (LinearIsometry.id : Space ι ℝ →ₗᵢ[ℝ] Space ι ℝ))).integral u =
      (HilbertTerminalIto.terminalIto F μ H b J).integral u := by
  apply HilbertIntegralUniqueness.integral_eq b
  intro j
  change (innerSL ℝ (b j)).compLpL 2 μ
    (HilbertTerminalIto.integral F μ H b (restrictNoise J (LinearIsometry.id : Space ι ℝ →ₗᵢ[ℝ] Space ι ℝ)) u)=
      (innerSL ℝ (b j)).compLpL 2 μ (HilbertTerminalIto.integral F μ H b J u)
  rw [HilbertTerminalIto.commutes,HilbertTerminalIto.commutes,restrictNoise_id]

/-- The existing Hilbert BDG theorem applies to the direct native
integral as well; identity noise restriction changes no integral. -/
theorem power_two (N : FiniteScalarIto.Family F μ H β) (e : HilbertBasis β ℝ (Space ι ℝ))
    (b : HilbertBasis κ ℝ E) (k : ℕ) :
    StandardTerminalBDGPower (2^k)
      (HilbertTerminalIto.terminalIto F μ H b (FiniteCylindricalIto.terminalIto N.toCoordinates e))
      (NativeScalarBDG.constant k) := by
  intro u
  rw [← integral_identity _ b u]
  exact NativeHilbertBDG.power_two N e (LinearIsometry.id : Space ι ℝ →ₗᵢ[ℝ] Space ι ℝ) b k u

end SHEStochastic.DirectHilbertBDG
