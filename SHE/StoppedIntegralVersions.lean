module

public import SHE.StandardFiniteIto
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.StoppedIntegralVersions
open MeasureTheory Set PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)

theorem stop_stop (t b : ℝ) (v : Process (E := C) 𝓕 μ h) :
    stop 𝓕 μ h t (stop 𝓕 μ h b v)=stop 𝓕 μ h (min t b) v := by
  apply Lp.ext
  have hs := ((Lp.memLp (stop 𝓕 μ h b v)).indicator (before_measurable 𝓕 t).nullMeasurableSet).coeFn_toLp
  have hb := ((Lp.memLp v).indicator (before_measurable 𝓕 b).nullMeasurableSet).coeFn_toLp
  have hm := ((Lp.memLp v).indicator (before_measurable 𝓕 (min t b)).nullMeasurableSet).coeFn_toLp
  filter_upwards [hs,hb,hm] with p hs hb hm
  have hs' : stop 𝓕 μ h t (stop 𝓕 μ h b v) p=(before t).indicator (stop 𝓕 μ h b v) p := hs
  have hb' : stop 𝓕 μ h b v p=(before b).indicator v p := hb
  have hm' : stop 𝓕 μ h (min t b) v p=(before (min t b)).indicator v p := hm
  rw [hs',hm']
  simp only [Set.indicator_apply,before,Set.mem_setOf_eq,lt_min_iff]
  by_cases ht : (p.1:ℝ) < t <;> by_cases hpb : (p.1:ℝ) < b <;> simp [ht,hpb,hb',before,Set.indicator_apply]

/-- An arbitrary finite vector of actual stopped scalar integrals has
an adapted version. This uses only the ordinary package-1 adapted
terminal-integral property, not a heat or word assumption. -/
theorem vectorIntegral_adapted_version
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h) {n : ℕ}
    (z : WordRecursion.State n) (R : Fin n → Process (E := C) 𝓕 μ h) (t : ℝ≥0) :
    ∃ V : Ω → WordRecursion.State n,StronglyMeasurable[𝓕 t] V ∧
      StandardFiniteIto.vectorIntegral 𝓕 μ h J z R t=ᵐ[μ] V := by
  classical
  choose V hV he using (fun i : Fin n => stopped_integral_adapted 𝓕 μ h J t (R i))
  let W : Ω → WordRecursion.State n := fun ω => WithLp.toLp 2 (fun i => z i+V i ω)
  have hW : StronglyMeasurable[𝓕 t] W := by
    letI : MeasurableSpace Ω := 𝓕 t
    apply Measurable.stronglyMeasurable
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    exact measurable_pi_iff.mpr (fun i => measurable_const.add (hV i).measurable)
  refine ⟨W,hW,?_⟩
  filter_upwards [ae_all_iff.mpr he] with ω hω
  ext i
  change z i+J.integral (stop 𝓕 μ h t (R i)) ω=z i+V i ω
  rw [hω i]

end SHE.StoppedIntegralVersions
