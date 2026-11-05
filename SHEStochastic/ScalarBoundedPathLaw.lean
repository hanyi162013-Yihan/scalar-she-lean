module

public import SHEStochastic.GlobalScalarVarianceNormalization
public import SHEStochastic.GlobalCanonicalFourierMildSolution
public import SHEStochastic.GlobalBoundedComparisonProof
public import SHEStochastic.CanonicalBrownianFamily

public import SHEStochastic.ScalarBoundedWellPosed

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarBoundedPathLaw
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier
  CanonicalStateDriverFiltration StoppedPathPasting
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace ScalarVarianceNormalization.Noise := borel _
local instance : BorelSpace ScalarVarianceNormalization.Noise := ⟨rfl⟩

variable {ι : Type} [Countable ι] [DecidableEq ι]


/-- Any two original scalar mild realizations with the same initial
profile induce the same continuous state-path law. -/
theorem laws_eq {Ω Ξ : Type} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΞ)
    (μ : Measure Ω) (ν : Measure Ξ) [pμ : IsProbabilityMeasure μ] [pν : IsProbabilityMeasure ν]
    (H : ℝ≥0) (hH : 0<H)
    {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ1 : β<1)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B)
    (ell : ℝ) (hell : 0<ell) (he : ∀ z,ell≤(g z)^2)
    (e : HilbertBasis ι ℝ ScalarVarianceNormalization.Noise) (u₀ : RealL2)
    (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι)
    (U : ℝ≥0→Ω→RealL2) (V : ℝ≥0→Ξ→RealL2)
    (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
    (hV : StronglyMeasurable[G.predictable] (Function.uncurry V))
    (hcU : ∀ x,Continuous (fun t => U t x)) (hcV : ∀ x,Continuous (fun t => V t x))
    (hiU : U 0 =ᵐ[μ] fun _ => u₀) (hiV : V 0 =ᵐ[ν] fun _ => u₀)
    (hmU : GlobalBoundedFourierRecognition.HasClosedVersion F μ H U hU hg hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) (U 0))
    (hmV : GlobalBoundedFourierRecognition.HasClosedVersion G ν H V hV hg hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto Q.toCoordinates e) (V 0)) :
    μ.map (NativeContinuousPath.path H U hcU)=ν.map (NativeContinuousPath.path H V hcV) := by
  let : SecondCountableTopology ScalarVarianceNormalization.Noise := e.repr.toHomeomorph.secondCountableTopology
  let D := BoundedScalarData.data hg hβ B hb ell hell he
  let X : Bool→Type := Bool.rec Ξ Ω
  let spaces : ∀ b,MeasurableSpace (X b) := Bool.rec mΞ mΩ
  let : ∀ b,MeasurableSpace (X b) := spaces
  let filters : ∀ b,Filtration ℝ≥0 (spaces b) := Bool.rec G F
  let measures : ∀ b,@Measure (X b) (spaces b) := Bool.rec ν μ
  let probabilities : ∀ b,IsProbabilityMeasure (measures b) := Bool.rec pν pμ
  let : ∀ b,IsProbabilityMeasure (measures b) := probabilities
  let J : ∀ b,@StandardTerminalIto (X b) RealL2 ℝ (spaces b) _ _ _ _ (filters b) (measures b) H := Bool.rec
    (restrictNoise (FiniteCylindricalIto.terminalIto Q.toCoordinates e) NativePhysicalState.push)
    (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) NativePhysicalState.push)
  let S : ∀ b,@SingleNativeHeatEquation.Data (X b) (spaces b) (filters b) (measures b) (probabilities b) H D (J b) u₀ := Bool.rec
    (GlobalBoundedNativeSingleEquation.data G ν H D V hV hg hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto Q.toCoordinates e) u₀ (V 0) hiV hcV hmV)
    (GlobalBoundedNativeSingleEquation.data F μ H D U hU hg hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) u₀ (U 0) hiU hcU hmU)
  let M : ∀ b,@NativeScalarModel.Model (X b) RealL2 (spaces b) _ _ _ (filters b) (measures b) (probabilities b) H (J b) := Bool.rec
    (NativeScalarModel.unitary (NativeScalarModel.ofFamily Q e) NativePhysicalState.equivalence)
    (NativeScalarModel.unitary (NativeScalarModel.ofFamily P e) NativePhysicalState.equivalence)
  have hEq := @NativeGlobalUniqueness.laws_eq Bool inferInstance inferInstance X spaces filters measures probabilities
    H hH D J u₀ S M true false
  exact congrArg (fun p => p.toMeasure) hEq

end SHEStochastic.ScalarBoundedPathLaw
