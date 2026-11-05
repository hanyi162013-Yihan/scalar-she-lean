module

public import SHEStochastic.MatrixUnboundedCompletedExitIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixUnboundedCompletedRemainder
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < (2 : ℝ)*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ S.law.toMeasure
    (MatrixBlockNaturalFiltration.filtration 1)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  MatrixUnboundedCompletedGlobal.completedSigma S

/-- Actual completed global state minus its deterministic initial heat orbit. -/
def value (T : ℝ≥0) (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Physical (d := Fin n) :=
  MatrixUnboundedCompletedGlobal.state S (T,ω) -
    VectorAnalyticHeat.heat (T : ℝ) (MatrixGlobalBlockPath.state 1 0 ω.2)

theorem decomposition (T : ℝ≥0)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    MatrixUnboundedCompletedGlobal.state S (T,ω) =
      VectorAnalyticHeat.heat (T : ℝ) (MatrixGlobalBlockPath.state 1 0 ω.2) + value S T ω := by
  simp only [value]
  abel

/-- The global Hilbert remainder has the literal unbounded matrix
Fourier Ito coefficient on the completed Brownian space. -/
theorem fourier_coordinate (H : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    (fun ω => MatrixFourierCoordinates.coordinate i a m (value S H ω)) =ᵐ[μc]
      fun ω => Real.exp (-(H : ℝ)*(m : ℝ)^2) *
        (FiniteCylindricalIto.terminalIto
          (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
          (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
          (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
            (MatrixUnboundedCompletedGlobal.state S)
            (MatrixUnboundedCompletedGlobal.predictable S)
            (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m) ω := by
  let c := Real.exp (-(H : ℝ)*(m : ℝ)^2)
  have hc : c*Real.exp ((H : ℝ)*(m : ℝ)^2)=1 := by
    unfold c
    rw [←Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have heq := MatrixUnboundedCompletedGlobal.equation S H i a m H le_rfl
  change (fun ω => Real.exp ((H : ℝ)*(m : ℝ)^2) *
      MatrixFourierCoordinates.coordinate i a m
        (MatrixUnboundedCompletedGlobal.state S (H,ω))) =ᵐ[μc]
    (fun ω => MatrixFourierCoordinates.coordinate i a m
      (MatrixGlobalBlockPath.state 1 0 ω.2) +
      (FiniteCylindricalIto.terminalIto
        (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
        (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
        (StoppedItoInputs.stop (Fc) μc H H
          (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
            (MatrixUnboundedCompletedGlobal.state S)
            (MatrixUnboundedCompletedGlobal.predictable S)
            (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m)) ω) at heq
  rw [FiniteItoStoppedVersions.stop_horizon] at heq
  filter_upwards [heq] with ω hω
  change Real.exp ((H : ℝ)*(m : ℝ)^2)*coordinate i a m
    (MatrixUnboundedCompletedGlobal.state S (H,ω))=coordinate i a m
      (MatrixGlobalBlockPath.state 1 0 ω.2)+_ at hω
  change coordinate i a m
    (MatrixUnboundedCompletedGlobal.state S (H,ω)-
      VectorAnalyticHeat.heat (H : ℝ) (MatrixGlobalBlockPath.state 1 0 ω.2)) = _
  rw [map_sub]
  have hheat := MatrixFourierCoordinates.coordinate_heat i a m H.property
    (MatrixGlobalBlockPath.state 1 0 ω.2)
  calc
    _ = coordinate i a m (MatrixUnboundedCompletedGlobal.state S (H,ω))-
          c*coordinate i a m (MatrixGlobalBlockPath.state 1 0 ω.2) := by
      exact congrArg (fun y : ℝ => coordinate i a m
        (MatrixUnboundedCompletedGlobal.state S (H,ω))-y) hheat
    _ = c*(Real.exp ((H : ℝ)*(m : ℝ)^2)*coordinate i a m
          (MatrixUnboundedCompletedGlobal.state S (H,ω))-
          coordinate i a m (MatrixGlobalBlockPath.state 1 0 ω.2)) := by
      rw [mul_sub,←mul_assoc,hc,one_mul]
    _ = _ := by rw [hω]; ring

/-- The same Fourier identification at an earlier time in a fixed
Brownian horizon, retaining the deterministic stopping of the input. -/
theorem fourier_coordinate_at (H T : ℝ≥0) (hTH : T≤H)
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    (fun ω => MatrixFourierCoordinates.coordinate i a m (value S T ω)) =ᵐ[μc]
      fun ω => Real.exp (-(T : ℝ)*(m : ℝ)^2) *
        (FiniteCylindricalIto.terminalIto
          (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
          (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
          (StoppedItoInputs.stop (Fc) μc H T
            (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
              (MatrixUnboundedCompletedGlobal.state S)
              (MatrixUnboundedCompletedGlobal.predictable S)
              (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m)) ω := by
  let c := Real.exp (-(T : ℝ)*(m : ℝ)^2)
  have hc : c*Real.exp ((T : ℝ)*(m : ℝ)^2)=1 := by
    unfold c
    rw [←Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have heq := MatrixUnboundedCompletedGlobal.equation S H i a m T hTH
  change (fun ω => Real.exp ((T : ℝ)*(m : ℝ)^2) *
      MatrixFourierCoordinates.coordinate i a m
        (MatrixUnboundedCompletedGlobal.state S (T,ω))) =ᵐ[μc]
    (fun ω => MatrixFourierCoordinates.coordinate i a m
      (MatrixGlobalBlockPath.state 1 0 ω.2) +
      (FiniteCylindricalIto.terminalIto
        (MatrixUnboundedCompletedGlobal.family S H).toCoordinates
        (MatrixPredictableHaarRotation.basis (d := Fin n))).integral
        (StoppedItoInputs.stop (Fc) μc H T
          (MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
            (MatrixUnboundedCompletedGlobal.state S)
            (MatrixUnboundedCompletedGlobal.predictable S)
            (MatrixUnboundedCompletedBeforeExitInput.global_energy S H) i a m)) ω) at heq
  filter_upwards [heq] with ω hω
  change Real.exp ((T : ℝ)*(m : ℝ)^2)*coordinate i a m
    (MatrixUnboundedCompletedGlobal.state S (T,ω))=coordinate i a m
      (MatrixGlobalBlockPath.state 1 0 ω.2)+_ at hω
  change coordinate i a m
    (MatrixUnboundedCompletedGlobal.state S (T,ω)-
      VectorAnalyticHeat.heat (T : ℝ) (MatrixGlobalBlockPath.state 1 0 ω.2)) = _
  rw [map_sub]
  have hheat := MatrixFourierCoordinates.coordinate_heat i a m T.property
    (MatrixGlobalBlockPath.state 1 0 ω.2)
  calc
    _ = coordinate i a m (MatrixUnboundedCompletedGlobal.state S (T,ω))-
          c*coordinate i a m (MatrixGlobalBlockPath.state 1 0 ω.2) := by
      exact congrArg (fun y : ℝ => coordinate i a m
        (MatrixUnboundedCompletedGlobal.state S (T,ω))-y) hheat
    _ = c*(Real.exp ((T : ℝ)*(m : ℝ)^2)*coordinate i a m
          (MatrixUnboundedCompletedGlobal.state S (T,ω))-
          coordinate i a m (MatrixGlobalBlockPath.state 1 0 ω.2)) := by
      rw [mul_sub,←mul_assoc,hc,one_mul]
    _ = _ := by rw [hω]; ring

end SHEStochastic.MatrixUnboundedCompletedRemainder
