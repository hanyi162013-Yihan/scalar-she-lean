module

public import SHE.PastItoAlgebra
public import SHE.StoppedDampingClock
public import SHE.TwoChannelItoRows
public import SHE.OrthogonalItoChannels
public import SHE.RotatedItoAlgebra
public import SHE.StandardFiniteIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.TwoChannelPastDifference
open MeasureTheory Set PredictableL2 PredictableItoRotation OrthogonalItoChannels StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
local instance : MeasurableSpace (Both C) := borel _
local instance : BorelSpace (Both C) := ⟨rfl⟩
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)


variable [CompleteSpace C]

theorem block_difference (A B D:Process (E:=C) 𝓕 μ h):
    TwoChannelItoRows.block 𝓕 μ h A B-TwoChannelItoRows.block 𝓕 μ h A D=
      processIsometry 𝓕 μ h (fun _=>right (C:=C)) (right_measurable 𝓕) (B-D):=by
  rw [TwoChannelItoRows.block,TwoChannelItoRows.block,map_sub]
  abel

/-- Ordinary post-v restriction commutes with the genuine deterministic
stopping operation inside the original predictable L2 space. -/
theorem stop_post (v q:ℝ≥0) (R:Process (E:=C) 𝓕 μ h):
    stop 𝓕 μ h q (PastItoInputs.post 𝓕 μ h v R)=
      PastItoInputs.post 𝓕 μ h v (stop 𝓕 μ h q R):=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [stop_ae 𝓕 μ h q (PastItoInputs.post 𝓕 μ h v R),
    PastItoInputs.post_ae 𝓕 μ h v R,
    PastItoInputs.post_ae 𝓕 μ h v (stop 𝓕 μ h q R),stop_ae 𝓕 μ h q R]
    with z hs hp hr hq
  rw [hs,hr]
  by_cases ht:z∈before (Ω:=Ω) (q:ℝ)
  · rw [indicator_of_mem ht,hp,hq,indicator_of_mem ht]
  · rw [indicator_of_notMem ht,hq,indicator_of_notMem ht]
    by_cases hv:v<z.1 <;> simp only [hv,ite_true,ite_false]

variable [IsProbabilityMeasure μ]

/-- The common additive channel cancels EXACTLY in the stopped post-v
reference difference, inside the original scalar Ito map. -/
theorem integral_difference (J:StandardTerminalIto (C:=Both C) (E:=ℝ) 𝓕 μ h)
    (v q:ℝ≥0) (A B D:Process (E:=C) 𝓕 μ h):
    J.integral (stop 𝓕 μ h q (PastItoInputs.post 𝓕 μ h v (TwoChannelItoRows.block 𝓕 μ h A B)))-
      J.integral (stop 𝓕 μ h q (PastItoInputs.post 𝓕 μ h v (TwoChannelItoRows.block 𝓕 μ h A D)))=
      (rightIntegral 𝓕 μ h J).integral (stop 𝓕 μ h q (PastItoInputs.post 𝓕 μ h v (B-D))):=by
  rw [←map_sub,←StoppedDampingClock.stop_sub,←PastItoAlgebra.post_sub,block_difference,
    PastItoAlgebra.post_isometry,←RotatedItoAlgebra.map_stop]
  rfl

end SHE.TwoChannelPastDifference
