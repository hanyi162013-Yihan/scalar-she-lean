module

public import SHE.FiniteReferenceSplice
public import SHE.StoppedInputAlgebra
public import SHE.StoppedIntegralVersions

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.FiniteSpliceStopCoherence
open Set MeasureTheory PredictableL2 StoppedItoInputs PastItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem stop_post (t : ℝ) (v : ℝ≥0) (u : Process (E:=C) 𝓕 μ H) :
    stop 𝓕 μ H t (post 𝓕 μ H v u)=post 𝓕 μ H v (stop 𝓕 μ H t u) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [stop_ae 𝓕 μ H t (post 𝓕 μ H v u),post_ae 𝓕 μ H v u,
    post_ae 𝓕 μ H v (stop 𝓕 μ H t u),stop_ae 𝓕 μ H t u] with p hs hp hr hu
  rw [hs,hr]
  by_cases ht : p∈before (Ω:=Ω) t
  · rw [indicator_of_mem ht,hu,indicator_of_mem ht]
    exact hp
  · rw [indicator_of_notMem ht,hu,indicator_of_notMem ht]
    split_ifs <;> rfl


variable {n : ℕ} (v : ℝ≥0) (R S : Fin n→Process (E:=C) 𝓕 μ H)

/-- Restricting the actual frozen splice preserves its original pre-v
and post-v parts. This is equality inside the SAME predictable L² space. -/
theorem stop_splice (t : ℝ) (i : Fin n) :
    stop 𝓕 μ H t (FiniteReferenceSplice.rows 𝓕 μ H v R S i)=
      FiniteReferenceSplice.rows 𝓕 μ H v (fun i=>stop 𝓕 μ H t (R i))
        (fun i=>stop 𝓕 μ H t (S i)) i := by
  rw [FiniteReferenceSplice.rows,TwoChannelItoRows.stop_add,stop_post,
    StoppedIntegralVersions.stop_stop,FiniteReferenceSplice.rows,StoppedIntegralVersions.stop_stop,min_comm]

theorem stop_joint (t : ℝ) (i : Fin (n+n)) :
    stop 𝓕 μ H t (FiniteReferenceSplice.jointRows 𝓕 μ H v R S i)=
      FiniteReferenceSplice.jointRows 𝓕 μ H v (fun i=>stop 𝓕 μ H t (R i))
        (fun i=>stop 𝓕 μ H t (S i)) i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [FiniteReferenceSplice.jointRows,Fin.append_left]
  · simpa only [FiniteReferenceSplice.jointRows,Fin.append_right] using stop_splice 𝓕 μ H v R S t j

end SHE.FiniteSpliceStopCoherence
