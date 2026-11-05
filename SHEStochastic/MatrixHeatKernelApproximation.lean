module

public import SHEStochastic.MatrixHeatColumnFlow
public import SHE.ApproximationClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixHeatKernelApproximation
open MeasureTheory Filter SHE SHE.ApproximationClock MatrixInfiniteHaar MatrixAnalyticKernel
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The original adapted cell construction applies to full matrix Haar
kernels: integrate only to the left endpoint and heat to the right one. -/
def approximant (n : ℕ) (t s : ℝ) (P : Profile d) : MatrixHaarKernel.Columns (d := d) :=
  if s ≤ left n t then kernel (right n t-s) P else 0

theorem tendsto {t s : ℝ} (ht : 0 < t) (P : Profile d) :
    Tendsto (fun n => approximant n t s P) atTop (𝓝 (kernel (t-s) P)) := by
  by_cases hs : s < t
  · have hk := (MatrixHeatColumnFlow.continuousAt_analytic (sub_pos.mpr hs) P).tendsto.comp
      ((right_tendsto ht.le).sub_const s)
    apply hk.congr'
    filter_upwards [(left_tendsto ht.le).eventually (lt_mem_nhds hs)] with n hn
    simp only [approximant,if_pos hn.le,Function.comp_apply]
  · have he (n : ℕ) : approximant n t s P=0 := by
      have hn : ¬ s ≤ left n t := not_le.mpr ((left_bounds n ht).2.1.trans_le (not_lt.mp hs))
      simp only [approximant,if_neg hn]
    simp only [he,MatrixAnalyticKernel.zero (sub_nonpos.mpr (not_lt.mp hs))]
    exact tendsto_const_nhds

theorem norm_le {t s : ℝ} (ht : 0 < t) (P : Profile d) (n : ℕ) :
    ‖approximant n t s P‖ ≤ ‖kernel (t-s) P‖ := by
  by_cases hs : s ≤ left n t
  · have hst : s < t := hs.trans_lt (left_bounds n ht).2.1
    have he := MatrixHeatColumnFlow.analytic_forward (sub_pos.mpr hst)
      (sub_nonneg.mpr (right_bounds n ht.le).1) P
    rw [show t-s+(right n t-t)=right n t-s by ring] at he
    rw [approximant,if_pos hs,he]
    exact MatrixHeatColumnFlow.contraction _ _
  · simp only [approximant,if_neg hs,norm_zero,norm_nonneg]

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩

theorem measurable {Z : Type*} [MeasurableSpace Z] (t s : Z → ℝ) (ht : Measurable t) (hs : Measurable s)
    (Q : Z → Profile d)
    (hQ : Measurable (fun z : Z × AddCircle (1 : ℝ) => (Q z.1).value z.2)) (n : ℕ) :
    Measurable (fun z => approximant n (t z) (s z) (Q z)) :=
  (MatrixAnalyticKernel.measurable _ (((right_measurable n).comp ht).sub hs) Q hQ).ite
    (measurableSet_le hs ((left_measurable n).comp ht)) measurable_const

end SHEStochastic.MatrixHeatKernelApproximation
