module
public import SHE.LeftFrozenFiniteHaarConsistency
public import SHE.LeftFrozenHaarInput
public import SHE.BoundedHilbertItoCell
public import SHE.FixedHaarIntegral
public import SHE.PredictableSteps
public import SHE.ContinuousPredictable
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.LeftFrozenFiniteHaarInput
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand LeftFrozenFiniteHaarKernel
open ApproximationCells
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable {a:ℝ→ℝ}(ha:Measurable a){ell M Holder β:ℝ}(hell:0<ell)
variable(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hHolder:0≤Holder)
variable(hholder:∀z w,|a z-a w|≤Holder*|z-w|^β)
variable(U:ℝ≥0→Ω→StateL2)(hUa:StronglyAdapted 𝓕 U)

def input(n:ℕ)(t:ℝ≥0):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  ((FiniteHaarColumnProjection.projection (E:=DyadicApproximation.RealL2)
    (FiniteHaar.nodesBelow n)).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕)))
    (LeftFrozenHaarInput.input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t)

theorem input_ae(n:ℕ)(t:ℝ≥0):
    input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t=ᵐ[energyMeasure μ H]
      (fun p=>value ha hell hb U n (t,p)):=by
  have hp:=ae_eq_of_ae_eq_trim
    ((FiniteHaarColumnProjection.projection (E:=DyadicApproximation.RealL2)
      (FiniteHaar.nodesBelow n)).coeFn_compLpL
      (LeftFrozenHaarInput.input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t))
  filter_upwards [hp,LeftFrozenHaarInput.input_ae 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t]
    with p hp hu
  change input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t p=_
  unfold input
  rw [hp,hu]
  rfl
end SHE.LeftFrozenFiniteHaarInput
