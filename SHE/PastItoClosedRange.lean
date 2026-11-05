module

public import SHE.PastItoContinuity
public import SHE.TerminalItoAverageWitness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.PastItoClosedRange
open Set Filter MeasureTheory PredictableL2 PastItoInputs
open scoped NNReal ENNReal
variable {Ω C:Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) (H v:ℝ≥0)

def projection:Process (E:=C) 𝓕 μ H→L[ℝ]Process (E:=C) 𝓕 μ H where
  toFun:=post 𝓕 μ H v
  map_add':=PastItoAlgebra.post_add 𝓕 μ H v
  map_smul':=PastItoAlgebra.post_smul 𝓕 μ H v
  cont:=(PastItoContinuity.lipschitz 𝓕 μ H v).continuous

def supported:Submodule ℝ (Process (E:=C) 𝓕 μ H):=
  (projection 𝓕 μ H v-ContinuousLinearMap.id ℝ (Process (E:=C) 𝓕 μ H)).ker

theorem mem_supported (input:Process (E:=C) 𝓕 μ H):
    input∈supported 𝓕 μ H v ↔ post 𝓕 μ H v input=input:=by
  change post 𝓕 μ H v input-input=0 ↔ _
  exact sub_eq_zero

theorem supported_closed:IsClosed (supported (C:=C) 𝓕 μ H v:Set (Process (E:=C) 𝓕 μ H)):=
  (projection 𝓕 μ H v-ContinuousLinearMap.id ℝ (Process (E:=C) 𝓕 μ H)).isClosed_ker

instance supported_complete:CompleteSpace (supported (C:=C) 𝓕 μ H v):=
  (supported_closed 𝓕 μ H v).completeSpace_coe

theorem post_idempotent (input:Process (E:=C) 𝓕 μ H):
    post 𝓕 μ H v (post 𝓕 μ H v input)=post 𝓕 μ H v input:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v input,post_ae 𝓕 μ H v (post 𝓕 μ H v input)] with z hz hi
  rw [hi,hz]
  split_ifs <;> rfl

theorem post_mem_supported (input:Process (E:=C) 𝓕 μ H):
    post 𝓕 μ H v input∈supported 𝓕 μ H v:=
  (mem_supported 𝓕 μ H v _).mpr (post_idempotent 𝓕 μ H v input)

variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

def integral:(supported (C:=C) 𝓕 μ H v)→ₗᵢ[ℝ]Lp ℝ 2 μ:=
  J.integral.comp (supported 𝓕 μ H v).subtypeₗᵢ

def range:Submodule ℝ (Lp ℝ 2 μ):=LinearMap.range (integral 𝓕 μ H v J).toLinearMap

theorem range_closed:IsClosed (range 𝓕 μ H v J:Set (Lp ℝ 2 μ)):=
  (integral 𝓕 μ H v J).isometry.isClosedEmbedding.isClosed_range

theorem post_integral_mem (input:Process (E:=C) 𝓕 μ H):
    J.integral (post 𝓕 μ H v input)∈range 𝓕 μ H v J:=
  ⟨⟨post 𝓕 μ H v input,post_mem_supported 𝓕 μ H v input⟩,rfl⟩

end SHE.PastItoClosedRange
