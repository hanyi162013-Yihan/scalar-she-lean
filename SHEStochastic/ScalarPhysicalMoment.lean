module

public import SHEStochastic.ScalarPhysicalDriftedLaw
public import SHEStochastic.ScalarStoppedMomentUniform

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPhysicalMoment
open MeasureTheory Set SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local notation "r" => NativeClock.rate
local notation "hr" => NativeClock.rate_pos
local notation "clk" => clock r hr
local notation "tm" => PredictableL2.timeMeasure
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω I : Type} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  (H : ℝ≥0) {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2) (e : HilbertBasis I ℝ Noise)
  (S : ScalarPhysicalDriftedLaw.Solution H hg hβ hβ₁ b u₀ e Ω)

/-- The physical solution has the original integrated second moment,
derived from its genuine stopped equations and the exact clock. -/
theorem integrable_sq :
    Integrable (fun p : ℝ≥0×Ω => ‖S.W p.1 p.2‖^2) (energyMeasure S.μ H) := by
  let _ : SecondCountableTopology Noise := e.repr.toHomeomorph.secondCountableTopology
  let U := ScalarUnitTorusStateClock.native S.W
  let hU := ScalarUnitTorusStateClock.predictable S.F S.W S.predictable
  let hc := ScalarUnitTorusStateClock.continuous_native S.W S.continuous
  let hnG := ScalarUnitTorusFourierClock.holder hg
  let bn := ScalarPhysicalDriftClock.native b
  obtain ⟨Q,hQ⟩ := NativeTimeDilatedFamily.exists_family S.F S.μ r hr H S.P e S.nulls
  have hPhys : ScalarPhysicalStoppedEquation.Equation S.F S.μ H hg hβ hβ₁ b u₀ (pullPath r hr U)
      (FiniteCylindricalIto.terminalIto S.P.toCoordinates e) := by
    rw [ScalarUnitTorusStateClock.pull_native]
    exact S.equation
  have hN := (ScalarPhysicalStoppedEquation.iff_native S.F S.μ H hg hβ hβ₁ b u₀ U hU hc
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e)
    (FiniteCylindricalIto.terminalIto S.P.toCoordinates e) hQ).mp hPhys
  obtain ⟨R,_,hR⟩ := ScalarStoppedMomentUniform.bound (H := r*H) hnG hβ hβ₁ bn u₀
  have hi := hR (filtration S.F (clk)) S.μ U hU hc
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e) _ hN
    (fun _ => measurable_const) (fun _ _ => by norm_num)
  have hM := ScalarStoppedMomentUniform.integrable_sq (filtration S.F (clk)) S.μ (r*H) U hU
    (hi.trans_lt ENNReal.ofReal_lt_top)
  let d := ENNReal.ofReal (r : ℝ)
  have hP : MeasurePreserving (fun p : ℝ≥0×Ω => (clk p.1,p.2))
      (d • energyMeasure S.μ H) (energyMeasure S.μ (r*H)) := by
    rw [energyMeasure,←Measure.prod_smul_left]
    exact (timeMeasure_clock_preserving r hr H).prod (MeasurePreserving.id S.μ)
  have h := hP.integrable_comp_of_integrable hM
  have hE : Integrable (fun p : ℝ≥0×Ω => ‖S.W p.1 p.2‖^2) (d • energyMeasure S.μ H) := by
    have he : (fun p : ℝ≥0×Ω => ‖U (clk p.1) p.2‖^2) =
        (fun p : ℝ≥0×Ω => ‖S.W p.1 p.2‖^2) := by
      funext p
      exact congrArg (fun a : RealL2 => ‖a‖^2)
        (congrFun (congrFun (ScalarUnitTorusStateClock.pull_native S.W) p.1) p.2)
    exact he ▸ h
  exact (integrable_smul_measure (ENNReal.ofReal_pos.mpr (show (0 : ℝ)<r from hr)).ne'
    ENNReal.ofReal_ne_top).mp hE

end SHEStochastic.ScalarPhysicalMoment
