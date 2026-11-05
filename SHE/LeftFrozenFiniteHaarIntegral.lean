module
public import SHE.LeftFrozenFiniteHaarConsistency
public import SHE.LeftFrozenHaarInput
public import SHE.BoundedHilbertItoCell
public import SHE.LeftFrozenFiniteHaarCells
public import SHE.LeftFrozenFiniteHaarOriginalLimit
public import SHE.FixedHaarIntegral
public import SHE.PredictableSteps
public import SHE.ContinuousPredictable
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.LeftFrozenFiniteHaarIntegral
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


theorem point_mono(n:ℕ){j k:ℕ}(hjk:j≤k):point n j≤point n k:=by
  change ApproximationClock.delta n*(j:ℝ)≤ApproximationClock.delta n*(k:ℝ)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) (ApproximationClock.delta_pos n).le

theorem cell_order(n:ℕ)(t:ℝ≥0)(k:ℕ)(hk:k∈Finset.Icc 1 (index n t)):
    point n (k-1)≤min (point n k) t:=by
  have hki:1 ≤ index n t:=(Finset.mem_Icc.mp hk).1.trans (Finset.mem_Icc.mp hk).2
  have ht0:0<(t:ℝ):=by
    have hh:=Nat.one_le_ceil_iff.mp hki
    change 0<(t:ℝ)/ApproximationClock.delta n at hh
    exact (div_pos_iff_of_pos_right (ApproximationClock.delta_pos n)).mp hh
  have ht':0<t:=by exact_mod_cast ht0
  apply le_min (point_mono n (Nat.sub_le k 1))
  have he:point n (index n t-1)<t:=by
    apply NNReal.coe_lt_coe.mp
    rw [←left_eq_point n ht']
    exact (ApproximationClock.left_bounds n ht0).2.1
  exact (point_mono n (Nat.sub_le_sub_right (Finset.mem_Icc.mp hk).2 1)).trans he.le

def value(n:ℕ)(t:ℝ≥0)(X:FiniteHaar.HaarNode→ℝ≥0→Ω→ℝ)(ω:Ω):StateL2:=
  ∑k∈Finset.Icc 1 (index n t),∑i∈FiniteHaar.nodesBelow n,
    (X i (min (point n k) t) ω-X i (point n (k-1)) ω) •
      LeftFrozenFiniteHaarCells.coefficient ha hell hb U n t k i ω

include hβ hHolder hholder hUa in
theorem integral_ae(n:ℕ)(t:ℝ≥0)
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hIJ:NativeObservationNaturality.StandardScalarNaturality I J)
    (hlocal:StandardTerminalPastLocality J):
    I.integral (LeftFrozenFiniteHaarInput.input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t)=ᵐ[μ]
      value ha hell hb U n t (fun i=>BoundedHilbertItoCell.driver 𝓕 μ H i J):=by
  have he:=LeftFrozenFiniteHaarCells.input_eq 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t
  rw [←he,LeftFrozenFiniteHaarCells.input,map_sum]
  have hm:=Lp.coeFn_fun_finsetSum (Finset.Icc 1 (index n t))
    (fun k=>I.integral (∑i∈FiniteHaar.nodesBelow n,
      LeftFrozenFiniteHaarCells.cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i))
  have hi:∀ᵐω∂μ,∀k:ℕ,
      I.integral (∑i∈FiniteHaar.nodesBelow n,
        LeftFrozenFiniteHaarCells.cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i) ω=
      ∑i∈FiniteHaar.nodesBelow n,I.integral
        (LeftFrozenFiniteHaarCells.cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i) ω:=by
    apply ae_all_iff.mpr
    intro k
    rw [map_sum]
    exact Lp.coeFn_fun_finsetSum _ _
  have hc:∀ᵐω∂μ,∀k∈Finset.Icc 1 (index n t),∀i:FiniteHaar.HaarNode,
      I.integral (LeftFrozenFiniteHaarCells.cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k i) ω=
      (BoundedHilbertItoCell.driver 𝓕 μ H i J (min (point n k) t) ω-
        BoundedHilbertItoCell.driver 𝓕 μ H i J (point n (k-1)) ω) •
        LeftFrozenFiniteHaarCells.coefficient ha hell hb U n t k i ω:=by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro hk
    apply ae_all_iff.mpr
    intro i
    exact BoundedHilbertItoCell.integral 𝓕 μ H _ _ i _
      (LeftFrozenFiniteHaarCells.coefficient_adapted 𝓕 ha hell hb hβ hHolder hholder U hUa n t k i)
      (LeftFrozenHaarInput.bound (M:=M) n t k)
      (LeftFrozenFiniteHaarCells.coefficient_bound ha hell hb U n t k i)
      (Real.sqrt_nonneg _) (cell_order n t k hk) I J hIJ hlocal
  filter_upwards [hm,hi,hc] with ω hm hi hc
  rw [hm]
  simp_rw [hi]
  exact Finset.sum_congr rfl (fun k hk=>Finset.sum_congr rfl (fun i _=>hc k hk i))
end SHE.LeftFrozenFiniteHaarIntegral
