module
public import SHE.LeftFrozenFiniteHaarConsistency
public import SHE.LeftFrozenHaarInput
public import SHE.BoundedHilbertItoCell
public import SHE.LeftFrozenFiniteHaarInput
public import SHE.FixedHaarIntegral
public import SHE.PredictableSteps
public import SHE.ContinuousPredictable
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.LeftFrozenFiniteHaarCells
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


def coefficient(n:ℕ)(t:ℝ≥0)(k:ℕ)(i:FiniteHaar.HaarNode)(ω:Ω):StateL2:=
  LeftFrozenHaarInput.coefficient ha hell hb U n t k ω i

include hβ hHolder hholder hUa in
theorem coefficient_adapted(n:ℕ)(t:ℝ≥0)(k:ℕ)(i:FiniteHaar.HaarNode):
    StronglyMeasurable[𝓕 (point n (k-1))] (coefficient ha hell hb U n t k i):=
  (lp.evalCLM ℝ (fun _:FiniteHaar.HaarNode=>DyadicApproximation.RealL2) 2 i).continuous.comp_stronglyMeasurable
    (LeftFrozenHaarInput.coefficient_adapted 𝓕 ha hell hb hβ hHolder hholder U hUa n t k)

theorem coefficient_bound(n:ℕ)(t:ℝ≥0)(k:ℕ)(i:FiniteHaar.HaarNode)(ω:Ω):
    ‖coefficient ha hell hb U n t k i ω‖≤LeftFrozenHaarInput.bound (M:=M) n t k:=
  (lp.norm_apply_le_norm (by norm_num:(2:ENNReal)≠0)
    (LeftFrozenHaarInput.coefficient ha hell hb U n t k ω) i).trans
      (LeftFrozenHaarInput.coefficient_bound ha hell hb U n t k ω)

def cell(n:ℕ)(t:ℝ≥0)(k:ℕ)(i:FiniteHaar.HaarNode):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  BoundedHilbertItoCell.input 𝓕 μ H (point n (k-1)) (min (point n k) t) i
    (coefficient ha hell hb U n t k i)
    (coefficient_adapted 𝓕 ha hell hb hβ hHolder hholder U hUa n t k i)
    (LeftFrozenHaarInput.bound (M:=M) n t k) (coefficient_bound ha hell hb U n t k i)

def input(n:ℕ)(t:ℝ≥0):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  ∑k∈Finset.Icc 1 (index n t),∑i∈FiniteHaar.nodesBelow n,
    cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i

include hβ hHolder hholder hUa in
theorem input_eq(n:ℕ)(t:ℝ≥0):
    input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t=
      LeftFrozenFiniteHaarInput.input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t:=by
  apply PastItoAlgebra.eq_of_ambient_ae 𝓕 μ H
  have hsum:=ae_eq_of_ae_eq_trim (Lp.coeFn_fun_finsetSum (Finset.Icc 1 (index n t))
    (fun k=>∑i∈FiniteHaar.nodesBelow n,cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i))
  have hinner:∀ᵐp∂energyMeasure μ H,∀k:ℕ,
      (∑i∈FiniteHaar.nodesBelow n,cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i) p=
      ∑i∈FiniteHaar.nodesBelow n,cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i p:=by
    apply ae_all_iff.mpr
    intro k
    exact ae_eq_of_ae_eq_trim (Lp.coeFn_fun_finsetSum (FiniteHaar.nodesBelow n) _)
  have hcell:∀ᵐp∂energyMeasure μ H,∀k:ℕ,∀i:FiniteHaar.HaarNode,
      cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i p=
      PredictableSteps.step (point n (k-1)) (min (point n k) t)
        (fun ω=>lp.single 2 i (coefficient ha hell hb U n t k i ω)) p:=by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro i
    exact BoundedHilbertItoCell.input_ae 𝓕 μ H _ _ _ _ _ _ _
  have hpos:∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,0<p.1:=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem H).mono (fun s hs=>hs.1))
  have hne:∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,p.1≠t:=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne t)
  filter_upwards [hsum,hinner,hcell,hpos,hne,
    LeftFrozenFiniteHaarInput.input_ae 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t]
    with p hs hi hc hp hn hv
  rw [hv]
  change (∑k∈Finset.Icc 1 (index n t),∑i∈FiniteHaar.nodesBelow n,
    cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i) p=_
  rw [hs]
  simp_rw [hi,hc]
  rw [value,←LeftFrozenHaarInput.raw_sum_eq ha hell hb U n t p.1 p.2 hp hn,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold PredictableSteps.step
  split_ifs
  · exact (FiniteHaarColumnProjection.projection_apply _ _).symm
  · simp only [Finset.sum_const_zero,map_zero]
end SHE.LeftFrozenFiniteHaarCells
