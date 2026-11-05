module

public import SHEStochastic.ScalarUnboundedFourierRecognition
public import SHEStochastic.UnboundedGlobalMildRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnboundedNativeExistence
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar
  MatrixInfiniteHaar AddCircle HeatParameterCover
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Vec" => Physical (d := Fin 1)
local notation "comp₀" => VectorHeatObservation.component (0 : Fin 1)
local notation "basis" => ScalarUnboundedFourierProjection.basis
local instance : SecondCountableTopology Vec := Lp.SecondCountableTopology
local instance : MeasurableSpace Vec := borel _
local instance : BorelSpace Vec := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin 1)) := borel _
local instance : BorelSpace (Input (d := Fin 1)) := ⟨rfl⟩

/-- The original scalar diffusion with strictly subunit Hölder exponent
admits a continuous weak realization of its localized native equation.
The square-integrable initial state need not be bounded. -/
theorem exists_native (H : ℝ≥0) (hH : 0<H)
    {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
    (u₀ : RealL2) (ell : ℝ) (hell : 0<ell) (he : ∀ z,ell≤(g z)^2) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (F : Filtration ℝ≥0 m) (μ : @Measure Ω m),
      ∃ (_ : IsProbabilityMeasure μ) (P : FiniteScalarIto.Family F μ H (Fin 1 × HaarNode))
        (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W)),
        (∀ ω, Continuous (fun t => W t ω)) ∧
        NullCompleteFiltration.ContainsNullSets F μ ∧
        (W 0 =ᵐ[μ] fun _ => u₀) ∧
        UnboundedGlobalNativeEquation.Equation F μ H W hW hg hβ hβ₁ P basis u₀ := by
  obtain ⟨R⟩ := ScalarUnboundedOneDimensional.exists_vector_realization hg hβ hβ₁ u₀ ell hell he
  let S := R.base
  let ρ : Measure Unit := Measure.dirac ()
  let Ω := RandomInitialBrownianFamily.Space ρ S.law.toMeasure
  let m : MeasurableSpace Ω := MatrixUnboundedCompletedGlobal.completedSigma S
  let μ := IndependentNoiseCompletion.measure ρ S.law.toMeasure
  let F := RandomInitialBrownianFamily.filtration ρ S.law.toMeasure
    (MatrixBlockNaturalFiltration.filtration 1)
  let P := MatrixUnboundedCompletedGlobal.family S H
  let U := MatrixUnboundedCompletedGlobal.state S
  have hU := MatrixUnboundedCompletedGlobal.predictable S
  let W := ScalarUnboundedFourierRecognition.state U
  have hW := ScalarUnboundedFourierRecognition.predictable U hU
  have hc (ω : Ω) : Continuous (fun t => W t ω) :=
    (comp₀).continuous.comp (MatrixGlobalBlockPath.continuous 1 zero_lt_one ω.2)
  have hnull := MatrixUnboundedCompletedGlobal.contains_null S
  have hE := MatrixUnboundedFourierPullback.energy
    (Ξ := Ω) (mΞ := m) Prod.snd
    (IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure)
    MatrixUnboundedGlobalFourierStep.state (MatrixUnboundedGlobalEnergy.finite_energy S H)
  have heq := ScalarUnboundedFourierRecognition.equation hg hβ hβ₁ U hU hE hH P hnull hc
    ((MatrixGlobalBlockPath.state 1 0) ∘ Prod.snd) (MatrixUnboundedCompletedGlobal.equation S H)
  have hi := (IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure).quasiMeasurePreserving.ae
    (MatrixUnboundedDeterministicMild.initial_ae (ScalarUnboundedOneDimensional.initial u₀) S)
  have hi' : W 0 =ᵐ[μ] fun _ => u₀ := by
    filter_upwards [hi] with ω hω
    change comp₀ (MatrixGlobalBlockPath.state 1 0 ω.2) = u₀
    change MatrixGlobalBlockPath.state 1 0 ω.2 = _ at hω
    rw [hω,ScalarUnboundedOneDimensional.initial_component]
  refine ⟨Ω,m,F,μ,inferInstance,P,W,hW,hc,hnull,hi',?_⟩
  intro N T δ hTH hδ hTD x
  filter_upwards [heq N T δ hTH hδ hTD x,hi'] with ω hw hi hbefore
  exact (hw hbefore).trans (congrArg (fun v : RealL2 =>
    NativeHeatObservation.functional (T+δ : ℝ≥0) x v +
      (FiniteCylindricalIto.terminalIto P.toCoordinates basis).integral
        (StoppedItoInputs.stop F μ H T
          (UnboundedGlobalNativeEquation.row F μ H W hW hg hβ hβ₁ N (T+δ) hTD x)) ω) hi)

end SHEStochastic.ScalarUnboundedNativeExistence
