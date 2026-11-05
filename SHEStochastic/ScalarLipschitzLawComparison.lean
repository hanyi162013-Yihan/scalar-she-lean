module

public import SHEStochastic.ScalarLipschitzClampedDriver
public import SHEStochastic.ScalarLipschitzFourierPullback
public import SHEStochastic.ScalarLipschitzNativeExistence
public import SHEStochastic.ScalarLipschitzSameNoise
public import SHEStochastic.ScalarDriftedNativeLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzLawComparison
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarCanonicalObservation ScalarDriftedNativeLaw ScalarLipschitzCanonicalDriver ScalarLipschitzConvolution
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "haar" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 haar
local notation "δ" => (Measure.dirac () : Measure Unit)
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {I : Type} [Countable I] [DecidableEq I] (H : ℝ≥0)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2) (e : HilbertBasis I ℝ Noise)

local notation "Fc" η => RandomInitialBrownianFamily.filtration δ η
  (CanonicalStateDriverFiltration.filtration (E := ℝ) (ι := I) H)
local notation "μc" η => IndependentNoiseCompletion.measure δ η

theorem model_eq {Ω : Type} [MeasurableSpace Ω]
    (hH : 0<H) (N : Model H hg zero_lt_one le_rfl b u₀ Ω I) (he : N.basis=e)
    (η : Measure (DriverSpace I H)) [IsProbabilityMeasure η] (hη : law N.P=η)
    (R : FiniteScalarIto.Family (CanonicalStateDriverFiltration.filtration (E := ℝ) (ι := I) H) η H I)
    (U : ℝ≥0 → Completed H η → RealL2)
    (hU : StronglyMeasurable[(Fc η).predictable] (Function.uncurry U))
    (hc : ∀ ω,Continuous (fun t => U t ω))
    (hEU : Integrable (fun p : ℝ≥0×Completed H η => ‖U p.1 p.2‖^2) (energyMeasure (μc η) H))
    (hEq : ScalarLipschitzZeroEquation.Equation e (completedFamily η R) hg U hU hEU u₀)
    (hR : ∀ i t,R.W i t=CanonicalStateDriverFiltration.coordinate H i t) :
    N.μ.map N.path=(μc η).map (NativeContinuousPath.path H U hc) := by
  let π := pull N.P η
  have hp : MeasurePreserving π N.μ (μc η) := pull_preserving N.P η hη N.nulls
  have hfil := pull_filtered N.P η hη N.nulls
  let P' := ScalarLipschitzClampedDriver.family N.P
  have hW : ∀ i t x,P'.W i t x=(completedFamily η R).W i t (π x) := by
    intro i t x
    change ScalarLipschitzClampedDriver.value N.P i t x=R.W i t (π x).2
    rw [hR]
    exact (coordinate_pull N.P η i t x).symm
  have hN := ScalarLipschitzZeroEquation.of_stopped N.basis N.P hg N.W N.predictable N.moment b u₀
    N.continuous N.nulls N.equation
  rw [he] at hN
  have hN' : ScalarLipschitzZeroEquation.Equation e P' hg N.W N.predictable N.moment u₀ := by
    intro ψ n t ht
    change (FiniteCylindricalIto.terminalIto P'.toCoordinates e).integral _ =ᵐ[N.μ] _
    rw [ScalarLipschitzClampedDriver.integral_eq N.P e]
    exact hN ψ n t ht
  have hP := ScalarLipschitzFourierPullback.equation π hp hfil e (completedFamily η R) P' hg U hU hEU
    hW u₀ hEq
  have hh := ScalarLipschitzSameNoise.laws_eq e P' hg N.W (ScalarLipschitzFourierPullback.state π U)
    N.predictable (ScalarLipschitzFourierPullback.predictable π hfil U hU)
    N.moment (ScalarLipschitzFourierPullback.energy π hp U hEU) u₀ hN' hP hH N.continuous
    (fun ω => hc (π ω))
  change N.μ.map N.path=N.μ.map (NativeContinuousPath.path H U hc ∘ π) at hh
  rw [hh,←Measure.map_map (NativeContinuousPath.measurable_path H U hc
    (hU.mono (predictable_le_product (Fc η))).measurable) hp.measurable,hp.map_eq]

/-- Two zero-drift models on arbitrary spaces have the same state law.
The single canonical strong solution is pulled back through both
original drivers, keeping the existing white-noise basis. -/
theorem zero_unique (hH : 0<H) : ZeroUnique H hg zero_lt_one le_rfl b u₀ e := by
  intro Ω Ξ _ _ M N hMb hNb _ _
  let η := law M.P
  let _ : IsProbabilityMeasure η := law_probability M.P
  let R := rawFamily M.P
  let P := completedFamily η R
  have hn := RandomInitialBrownianFamily.contains_null δ η
    (CanonicalStateDriverFiltration.filtration (E := ℝ) (ι := I) H)
  obtain ⟨U,hU,hc,hEU,_,hFix⟩ := ScalarLipschitzNativeExistence.exists_mild e P hg hH hn u₀
  have hEI (t : ℝ≥0) (ht : t≤H) :
      Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure (μc η) H) :=
    (hFix t ht).choose
  have he := ScalarLipschitzFourierMild.stopped e P hg U hU b u₀ hc hn hEU hEI
    (fun t ht => (hFix t ht).choose_spec)
  have hEq := ScalarLipschitzZeroEquation.of_stopped e P hg U hU hEU b u₀ hc hn he
  have hleft := model_eq H hg b u₀ e hH M hMb η rfl R U hU hc hEU hEq (fun _ _ => rfl)
  have hright := model_eq H hg b u₀ e hH N hNb η (law_eq N.P M.P) R U hU hc hEU hEq (fun _ _ => rfl)
  exact hleft.trans hright.symm

end SHEStochastic.ScalarLipschitzLawComparison
