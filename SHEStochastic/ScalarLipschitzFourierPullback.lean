module

public import SHEStochastic.ScalarLipschitzZeroEquation
public import SHEStochastic.CylindricalProcessPullback

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzFourierPullback
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "haar" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 haar
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω Ξ I : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 mΩ} {D : Filtration ℝ≥0 mΞ}
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}
  (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ) (hfil : ∀ t,@Measurable Ξ Ω (D t) (F t) π)
  (e : HilbertBasis I ℝ Noise)
  (P : FiniteScalarIto.Family F μ H I) (Q : FiniteScalarIto.Family D ν H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
  (hM : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H))

def state (t : ℝ≥0) (x : Ξ) : RealL2 := U t (π x)

include hfil hU in
theorem predictable :
    StronglyMeasurable[D.predictable] (Function.uncurry (state π U)) :=
  hU.comp_measurable (FilteredPullback.predictable_map π hfil)

omit [IsProbabilityMeasure μ] in
include hπ hM in
theorem energy :
    Integrable (fun p : ℝ≥0×Ξ => ‖state π U p.1 p.2‖^2) (energyMeasure ν H) :=
  ((MeasurePreserving.id (PredictableL2.timeMeasure H)).prod hπ).integrable_comp_of_integrable hM

include hπ hfil in
/-- The unstopped scalar Fourier equation is natural under the same
completed, filtered Brownian pullback as the native integral. -/
theorem equation (hW : ∀ i t x,Q.W i t x=P.W i t (π x))
    (u₀ : RealL2) (hEq : ScalarLipschitzZeroEquation.Equation e P hg U hU hM u₀) :
    ScalarLipschitzZeroEquation.Equation e Q hg (state π U)
      (predictable π hfil U hU) (energy π hπ U hM) u₀ := by
  intro ψ n t ht
  let u := ScalarGrowingFourierInput.input F μ H U hU hg zero_lt_one le_rfl ψ n hM
  let v := ScalarGrowingFourierInput.input D ν H (state π U) (predictable π hfil U hU)
    hg zero_lt_one le_rfl ψ n (energy π hπ U hM)
  have hp : MeasurePreserving (FilteredPullback.timeMap π) (energyMeasure ν H) (energyMeasure μ H) :=
    (MeasurePreserving.id (PredictableL2.timeMeasure H)).prod hπ
  have hr : StoppedItoInputs.stop D ν H t v =ᵐ[energyMeasure ν H]
      fun p => (LinearIsometry.id : Noise →ₗᵢ[ℝ] Noise)
        (StoppedItoInputs.stop F μ H t u (FilteredPullback.timeMap π p)) := by
    filter_upwards [StoppedItoInputs.stop_ae D ν H t v,
      hp.quasiMeasurePreserving.ae (StoppedItoInputs.stop_ae F μ H t u),
      ScalarGrowingFourierInput.input_ae D ν H (state π U) (predictable π hfil U hU)
        hg zero_lt_one le_rfl ψ n (energy π hπ U hM),
      hp.quasiMeasurePreserving.ae (ScalarGrowingFourierInput.input_ae F μ H U hU hg
        zero_lt_one le_rfl ψ n hM)] with p hnv hnu hv hu
    rw [hnv,LinearIsometry.id_apply,hnu]
    change (StoppedItoInputs.before (Ω := Ξ) (t : ℝ)).indicator v p =
      (StoppedItoInputs.before (Ω := Ω) (t : ℝ)).indicator u (FilteredPullback.timeMap π p)
    by_cases ht' : (p.1 : ℝ)<t
    · rw [indicator_of_mem (show p∈StoppedItoInputs.before (t : ℝ) from ht'),
        indicator_of_mem (show FilteredPullback.timeMap π p∈StoppedItoInputs.before (t : ℝ) from ht')]
      exact hv.trans hu.symm
    · rw [indicator_of_notMem (show p∉StoppedItoInputs.before (t : ℝ) from ht'),
        indicator_of_notMem (show FilteredPullback.timeMap π p∉StoppedItoInputs.before (t : ℝ) from ht')]
  have hj := CylindricalPullback.process_naturality π hπ hfil P Q e e LinearIsometry.id id
    (fun _ => rfl) hW (StoppedItoInputs.stop F μ H t u) (StoppedItoInputs.stop D ν H t v) hr
  exact hj.trans (hπ.quasiMeasurePreserving.ae (hEq ψ n t ht))

end SHEStochastic.ScalarLipschitzFourierPullback
