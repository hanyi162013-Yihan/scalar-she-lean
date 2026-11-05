module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ClosedIntervalRange
open Set Filter MeasureTheory
open scoped Topology

/-- An a.e. closed-subspace constraint on an open time interval persists
at its lower endpoint when the actual row is right-continuous there. -/
theorem endpoint_mem {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (S : Submodule ℝ F) [S.HasOrthogonalProjection]
    {lo hi mid : ℝ} (hlm : lo < mid) (hmh : mid ≤ hi) (f : ℝ → F)
    (hc : ContinuousOn f (Icc lo mid))
    (hae : ∀ᵐ r ∂volume.restrict (Ioc lo hi), f r ∈ S) : f lo ∈ S := by
  let T := Sᗮ.orthogonalProjectionOnto
  have hz : (fun r => T (f r)) =ᵐ[volume.restrict (Icc lo mid)] fun _ => 0 := by
    have hh := (ae_restrict_iff' measurableSet_Ioc).mp hae
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hh, volume.ae_ne lo] with r hr hn hmem
    have hri : r ∈ Ioc lo hi := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hn), hmem.2.trans hmh⟩
    exact Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero (hr hri)
  have hT : ContinuousOn (fun r => T (f r)) (Icc lo mid) := T.continuous.comp_continuousOn hc
  have hclosure : Icc lo mid ⊆ closure (interior (Icc lo mid)) := by
    rw [interior_Icc, closure_Ioo hlm.ne]
  have heq := Measure.eqOn_of_ae_eq hz hT continuousOn_const hclosure
  have he := heq (show lo ∈ Icc lo mid from ⟨le_rfl, hlm.le⟩)
  have hs := (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp he
  simpa only [Submodule.orthogonal_orthogonal] using hs

end SHE.ClosedIntervalRange
