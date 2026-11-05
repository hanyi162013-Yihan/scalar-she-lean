module

public import SHEStochastic.PathIntegratedCovariance
public import Mathlib.Topology.MetricSpace.UniformConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.ContinuousPathIntegral
open MeasureTheory Filter StoppedPathPasting PastedGeneratorFunctional Set
open scoped NNReal Topology
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    (H : ℝ≥0) (w : BoundedContinuousFunction ℝ ℝ)

/-- A continuous state functional need not be globally bounded to have
a well-defined time integral along every continuous finite-horizon path. -/
def value (b : C(E,ℝ)) (x : Path H E) (t : Time H) : ℝ :=
  ∫ s in 0..t.val,w s*b (read H x s)

theorem continuous (b : C(E,ℝ)) :
    Continuous (fun p : Path H E×Time H => value H w b p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (w.continuous.comp continuous_snd).mul
      (b.continuous.comp (continuous_eval.comp (continuous_fst.fst.prodMk
        ((continuous_projIcc (h := H.property)).comp continuous_snd))))
  · exact continuous_subtype_val.comp continuous_snd

/-- Compact-uniform convergence of state functionals passes to their
weighted time integrals, uniformly in the observation time and in every
compact collection of paths. No global coefficient cap is assumed. -/
theorem uniformly_on_compact (bn : ℕ → C(E,ℝ)) (b : C(E,ℝ))
    (hb : ∀ s : Set E,IsCompact s → TendstoUniformlyOn (fun m => bn m) b atTop s)
    {K : Set (Path H E)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun (m : ℕ) (p : Path H E×Time H) => value H w (bn m) p.1 p.2)
      (fun p => value H w b p.1 p.2) atTop (K×ˢSet.univ) := by
  let S : Set E := (fun z : Path H E×Time H => z.1 z.2) '' (K×ˢSet.univ)
  have hS : IsCompact S := (hK.prod isCompact_univ).image continuous_eval
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ : ℝ := ε/(1+‖w‖*(H : ℝ))
  have hden : 0<1+‖w‖*(H : ℝ) := by positivity
  have hδ : 0<δ := div_pos hε hden
  have hm := Metric.tendstoUniformlyOn_iff.mp (hb S hS) δ hδ
  filter_upwards [hm] with m hm p hp
  have hi (c : C(E,ℝ)) : IntervalIntegrable (fun s => w s*c (read H p.1 s)) volume 0 p.2.val :=
    (w.continuous.mul (c.continuous.comp (continuous_read H p.1))).intervalIntegrable 0 p.2.val
  have he : value H w (bn m) p.1 p.2-value H w b p.1 p.2=
      ∫ s in 0..p.2.val,w s*((bn m) (read H p.1 s)-b (read H p.1 s)) := by
    rw [value,value,←intervalIntegral.integral_sub (hi (bn m)) (hi b)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [dist_eq_norm,norm_sub_rev,he]
  have hbound : ‖∫ s in 0..p.2.val,w s*((bn m) (read H p.1 s)-b (read H p.1 s))‖≤
      (‖w‖*δ)*|p.2.val-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le p.2.property.1] at hs
    have hsH : s∈Set.Icc (0 : ℝ) (H : ℝ) := ⟨hs.1.le,hs.2.trans p.2.property.2⟩
    have hmem : read H p.1 s∈S := by
      refine ⟨(p.1,⟨s,hsH⟩),⟨hp.1,Set.mem_univ _⟩,?_⟩
      exact (read_val H p.1 ⟨s,hsH⟩).symm
    have hd := hm (read H p.1 s) hmem
    rw [dist_eq_norm,norm_sub_rev] at hd
    rw [norm_mul]
    exact mul_le_mul (w.norm_coe_le_norm s) hd.le (norm_nonneg _) (norm_nonneg _)
  have htime : |p.2.val-0|≤H := by
    rw [sub_zero,abs_of_nonneg p.2.property.1]
    exact p.2.property.2
  have hsmall : ‖w‖*δ*(H : ℝ)<ε := by
    have hmul : δ*(1+‖w‖*(H : ℝ))=ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  exact (hbound.trans (mul_le_mul_of_nonneg_left htime (by positivity))).trans_lt hsmall

end SHEStochastic.ContinuousPathIntegral
