module
public import SHE.BoundedHaarRowApproximation
public import SHE.FiniteHaarProjectionL2
public import SHE.CanonicalScalarItoSums
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.CanonicalBoundedHaarIdentification
open MeasureTheory Set PredictableL2 ApproximationCells FiniteHaar CanonicalContinuousStateDriver
open scoped NNReal ENNReal Topology
local instance identification_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance identification_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω E:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
  [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(H q:ℝ≥0)(R:Iic q×E→RealHaarInput)(hR:Continuous R)
variable(U:ℝ≥0→Ω→E)(hUa:StronglyAdapted 𝓕 U)(M:ℝ)(hb:∀p,‖R p‖≤M)

def time(n k:ℕ):ℝ≥0:=BoundedRowStepInputs.time q n k
def row(n k:ℕ)(u:E):RealHaarInput:=R (⟨time q n k,min_le_right _ _⟩,u)
def indices(n:ℕ):Finset (ℕ×HaarNode):=(Finset.range (index n q)).product (nodesBelow n)
def projected(n:ℕ):Process (E:=RealHaarInput) 𝓕 μ H:=
  BoundedHaarRowApproximation.input 𝓕 μ H q R hR U hUa M hb n

private theorem sum_shift{A:Type*}[AddCommMonoid A](m:ℕ)(f:ℕ→A):
    (∑k∈Finset.Icc 1 m,f k)=∑k∈Finset.range m,f (k+1):=by
  classical
  apply Finset.sum_bij (fun k _=>k-1)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hk l hl he
    simp only [Finset.mem_Icc] at hk hl
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨k+1,?_,by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    congr 1
    omega

include hR in
theorem row_measurable(n k:ℕ):Measurable (row q R n k):=
  hR.measurable.comp (measurable_const.prodMk measurable_id)

theorem time_le(n k:ℕ)(hq:q≤H):time q n k≤H:=(min_le_right _ _).trans hq

theorem time_mono(n k:ℕ):time q n k≤time q n (k+1):=by
  apply min_le_min_right
  change ApproximationClock.delta n*(k:ℝ)≤ApproximationClock.delta n*((k+1:ℕ):ℝ)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k) (ApproximationClock.delta_pos n).le

/-- The actual finite predictable projection has exactly the canonical
strict-cell Haar row. All deterministic cell endpoints are discarded by
proved time nullity, and the cell indexing is reconciled explicitly. -/
theorem projected_ae(n:ℕ):projected 𝓕 μ H q R hR U hUa M hb n=ᵐ[energyMeasure μ H]
    (fun p=>∑j∈indices q n,if time q n j.1<p.1 ∧ p.1<time q n (j.1+1) then
      (row q R n j.1 (U (time q n j.1) p.2) j.2) • lp.single 2 j.2 (1:ℝ) else 0):=by
  classical
  have hp:projected 𝓕 μ H q R hR U hUa M hb n=ᵐ[energyMeasure μ H]
      (fun p=>FiniteHaarColumnProjection.projection (nodesBelow n)
        (BoundedRowStepInputs.input 𝓕 μ H q R hR U hUa M hb n p)):=by
    apply ae_eq_of_ae_eq_trim
    letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    exact FiniteHaarProjectionL2.projection_ae
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) (nodesBelow n)
      (BoundedRowStepInputs.input 𝓕 μ H q R hR U hUa M hb n)
  have hn:∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,∀k:ℕ,p.1≠time q n k:=
    ae_all_iff.mpr (fun k=>Measure.quasiMeasurePreserving_fst.ae ((PredictableL2.timeMeasure H).ae_ne _))
  filter_upwards [hp,BoundedRowStepInputs.input_ae 𝓕 μ H q R hR U hUa M hb n,hn] with p hp hi hn
  change projected 𝓕 μ H q R hR U hUa M hb n p=_
  rw [hp,hi,map_sum,sum_shift,indices]
  erw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  have hright:p.1≤time q n (k+1) ↔p.1<time q n (k+1):=
    ⟨fun hh=>lt_of_le_of_ne hh (hn (k+1)),le_of_lt⟩
  simp only [Nat.add_sub_cancel,BoundedRowStepInputs.coefficient,PredictableSteps.step,mem_Ioc]
  change FiniteHaarColumnProjection.projection (nodesBelow n)
    (if time q n k<p.1 ∧ p.1≤time q n (k+1) then row q R n k (U (time q n k) p.2) else 0)=_
  simp only [hright]
  by_cases hc:time q n k<p.1 ∧ p.1<time q n (k+1)
  · simp only [hc,and_self,ite_true,FiniteHaarColumnProjection.projection_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [row,smul_eq_mul,mul_one] using
      (lp.single_smul (E:=fun _:HaarNode=>ℝ) (𝕜:=ℝ) 2 i (R (⟨time q n k,min_le_right _ _⟩,U (time q n k) p.2) i) (1:ℝ))
  · simp only [hc,ite_false,map_zero,Finset.sum_const_zero]

/-- The SAME actual stochastic integral of the convergent projected row
is the explicit measurable finite state-and-driver Haar sum. No
stochastic path-functional representation is assumed. -/
theorem integral_eq(n:ℕ)(hq:q≤H)(hM:0≤M)
    (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)(hlocal:StandardTerminalPastLocality J)
    (hc:∀ω,Continuous (fun t=>U t ω))
    (W:HaarNode→ℝ≥0→Ω→ℝ)(hWc:∀i ω,Continuous (fun t=>W i t ω))
    (hW:∀i k,W i (time q n k)=ᵐ[μ] CanonicalScalarItoCells.coordinate H i 𝓕 μ J (time q n k)):
    J.integral (projected 𝓕 μ H q R hR U hUa M hb n)=ᵐ[μ]
      (fun ω=>CanonicalScalarItoSums.value H (time q n) (fun k=>time_le H q n k hq)
        (row q R n) (indices q n) (bundle H U hc W hWc ω)):=by
  obtain ⟨f,hf,hi⟩:=CanonicalScalarItoSums.exists_input H (time q n) (fun k=>time_le H q n k hq)
    (row q R n) (indices q n) 𝓕 μ J (time_mono q n) (row_measurable q R hR n)
    M hM (fun k u=>hb _) hlocal U hc hUa W hWc hW
  have he:f=projected 𝓕 μ H q R hR U hUa M hb n:=
    PastItoAlgebra.eq_of_ambient_ae 𝓕 μ H (hf.trans (projected_ae 𝓕 μ H q R hR U hUa M hb n).symm)
  rw [he] at hi
  exact hi
end SHE.CanonicalBoundedHaarIdentification
