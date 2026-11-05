module

public import SHE.MeasurableL2Field
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HilbertColumns
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology

abbrev Space (I E : Type*) [NormedAddCommGroup E] := lp (fun _ : I => E) 2

section Basic
variable {I E : Type*} [NormedAddCommGroup E]

def ofSummable (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) : Space I E :=
  ⟨v,memℓp_gen (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hv)⟩

theorem norm_sq (v : Space I E) : ‖v‖^2=∑' i,‖v i‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal) v

theorem dist_eq (v w : Space I E) : dist v w=Real.sqrt (∑' i,‖v i-w i‖^2) := by
  have he := norm_sq (v-w)
  simp only [lp.coeFn_sub,Pi.sub_apply] at he
  rw [dist_eq_norm,← he,Real.sqrt_sq (norm_nonneg _)]

end Basic

section Separable
variable {I E : Type*} [Countable I] [NormedAddCommGroup E] [SecondCountableTopology E]

/-- Countably many actual Hilbert-space columns form a separable L²
space. This proves the topological hypothesis needed for Borel stochastic
integrands, using genuine finite-column approximation in norm. -/
instance space_separable : SeparableSpace (Space I E) := by
  classical
  let K (s : Finset I) (v : s → E) : Space I E := ∑ i : s,lp.single 2 i (v i)
  have hK (s : Finset I) : Continuous (K s) := by
    apply continuous_finsetSum
    intro i _
    exact (lp.isometry_single (p := 2) (i:I)).continuous.comp (continuous_apply i)
  let A : Set (Space I E) := ⋃ s : Finset I,range (K s)
  have hA : IsSeparable A := IsSeparable.iUnion (fun s => isSeparable_range (hK s))
  have hc (v : Space I E) : v ∈ closure A := by
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ⊤) v)
    apply Eventually.of_forall
    intro s
    apply subset_closure
    apply mem_iUnion.mpr
    refine ⟨s,fun i => v i,?_⟩
    exact Finset.sum_coe_sort s (fun i => lp.single 2 i (v i))
  apply isSeparable_univ_iff.mp
  exact hA.closure.mono (fun v _ => hc v)

instance space_secondCountable : SecondCountableTopology (Space I E) :=
  UniformSpace.secondCountable_of_separable _

end Separable

section Measurable
variable {P I E : Type*} [MeasurableSpace P] [Countable I]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_of_columns {K : P → Space I E} (hK : ∀ i,Measurable (fun p => K p i)) :
    @Measurable P (Space I E) _ (borel (Space I E)) K := by
  let : MeasurableSpace (Space I E) := borel (Space I E)
  let : BorelSpace (Space I E) := ⟨rfl⟩
  apply MeasurableL2Field.measurable_of_dist
  intro v
  have hm : Measurable (fun p => Real.sqrt (∑' i,‖K p i-v i‖^2)) :=
    (Measurable.tsum (fun i => ((hK i).sub measurable_const).norm.pow_const (2:ℕ))).sqrt
  have heq : (fun p => dist (K p) v)=(fun p => Real.sqrt (∑' i,‖K p i-v i‖^2)) :=
    funext (fun p => dist_eq (K p) v)
  rw [heq]
  exact hm

end Measurable
end SHE.HilbertColumns
