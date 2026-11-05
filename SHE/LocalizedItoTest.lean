module

public import SHE.StateCutoff
public import SHE.ParameterSmoothContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.LocalizedItoTest
open MeasureTheory Set Filter GaussianItoTest UniformSmooth
open scoped Topology ENNReal
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def localized (n : ℕ) (G : ℝ→E→ℝ) (t : ℝ) (z : E) : ℝ :=
  StateCutoff.cutoff ((n:ℝ)+1) z*G t z

theorem uniform_localized {G : ℝ→E→ℝ} (hG : UniformBoundedSmooth G) :
    UniformBoundedSmooth (fun p : ℕ×ℝ => localized p.1 G p.2) := by
  have hc : UniformBoundedSmooth (fun p : ℕ×ℝ => StateCutoff.cutoff (E := E) ((p.1:ℝ)+1)) := by
    refine ⟨fun p => StateCutoff.smooth _,fun k => ?_⟩
    obtain ⟨B,hB,hbound⟩ := StateCutoff.uniform_derivative_bound (E := E) k
    exact ⟨B,hB,fun p z => hbound _ (by have := Nat.cast_nonneg (α := ℝ) p.1; linarith) z⟩
  have hg : UniformBoundedSmooth (fun p : ℕ×ℝ => G p.2) := by
    refine ⟨fun p => hG.smooth p.2,fun k => ?_⟩
    obtain ⟨B,hB,hbound⟩ := hG.bounds k
    exact ⟨B,hB,fun p z => hbound p.2 z⟩
  exact hc.mul hg

theorem fixed_uniform {G : ℝ→E→ℝ} (hG : UniformBoundedSmooth G) (n : ℕ) :
    UniformBoundedSmooth (localized n G) := by
  have hh := uniform_localized hG
  refine ⟨fun t => hh.smooth (n,t),fun k => ?_⟩
  obtain ⟨B,hB,hbound⟩ := hh.bounds k
  exact ⟨B,hB,fun t z => hbound (n,t) z⟩

theorem localized_eventuallyEq (n : ℕ) (G : ℝ→E→ℝ) (t : ℝ) {z : E} (hz : ‖z‖<(n:ℝ)+1) :
    localized n G t=ᶠ[𝓝 z] G t := by
  filter_upwards [StateCutoff.eventuallyEq_one (by positivity : 0<(n:ℝ)+1) hz] with w hw
  rw [localized,hw,one_mul]

theorem localized_jets_eq (n : ℕ) (G : ℝ→E→ℝ) (t : ℝ) {z : E} (hz : ‖z‖<(n:ℝ)+1) :
    localized n G t z=G t z ∧ fderiv ℝ (localized n G t) z=fderiv ℝ (G t) z ∧
      GaussianTaylor.hessian (localized n G t) z=GaussianTaylor.hessian (G t) z := by
  have he := localized_eventuallyEq n G t hz
  exact ⟨he.eq_of_nhds,he.fderiv_eq,(he.fderiv).fderiv_eq⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- Deterministic smooth tests with a genuine time derivative allowed
linear state growth. State localization below supplies the bounded
ordinary Itô test hypotheses, rather than assuming a larger formula. -/
structure SmoothTimeTest (a b : ℝ) (G dG : ℝ→E→ℝ) : Prop where
  continuous : Continuous (fun p : ℝ×E => G p.1 p.2)
  uniformSmooth : UniformBoundedSmooth G
  time_absolutelyContinuous : ∀ z,AbsolutelyContinuousOnInterval (fun t => G t z) a b
  time_derivative : ∀ᵐ t : ℝ,t∈Ioo a b → ∀ z,HasDerivAt (fun r => G r z) (dG t z) t
  derivative_measurable : Measurable (fun p : ℝ×E => dG p.1 p.2)
  derivative_state_continuous : ∀ t,Continuous (dG t)
  derivative_envelope : ∃ v : ℝ→ℝ,IntervalIntegrable v volume a b ∧
    ∀ t∈Ioo a b,0≤v t ∧ ∀ z,‖dG t z‖≤v t*(1+‖z‖)

theorem regular_localized {k : ℕ} {a b : ℝ} {G dG : ℝ→WordRecursion.State k→ℝ}
    (hG : SmoothTimeTest a b G dG) (n : ℕ) :
    RegularTest a b (localized n G) (localized n dG) := by
  have hs := fixed_uniform hG.uniformSmooth n
  have hc : Continuous (fun p : ℝ×WordRecursion.State k => localized n G p.1 p.2) :=
    ((StateCutoff.smooth ((n:ℝ)+1)).continuous.comp continuous_snd).mul hG.continuous
  obtain ⟨B,hB,hDb⟩ := hs.fderiv.fderiv.norm_bound
  refine ⟨hc,fun t => (hs.smooth t).of_le (by simp),
    ParameterSmoothContinuity.continuous_fderiv (localized n G) hc
      (fun t => (hs.smooth t).of_le (by simp)) hB hDb,
    ParameterSmoothContinuity.continuous_hessian (localized n G) hc hs,
    fun z => AbsolutelyContinuousOnInterval.const_mul _ (hG.time_absolutelyContinuous z),
    ?_,?_,?_,?_,?_⟩
  · filter_upwards [hG.time_derivative] with t ht hmem z
    exact (ht hmem z).const_mul (StateCutoff.cutoff ((n:ℝ)+1) z)
  · exact (((StateCutoff.smooth ((n:ℝ)+1)).continuous.comp continuous_snd).measurable).mul hG.derivative_measurable
  · intro t
    exact (StateCutoff.smooth ((n:ℝ)+1)).continuous.mul (hG.derivative_state_continuous t)
  · obtain ⟨v,hvi,hv⟩ := hG.derivative_envelope
    refine ⟨fun t => v t*(1+2*((n:ℝ)+1)),hvi.mul_const _,fun t ht z => ?_⟩
    have hv0 := (hv t ht).1
    by_cases hz : StateCutoff.cutoff ((n:ℝ)+1) z=0
    · rw [localized,hz,zero_mul,norm_zero]
      exact mul_nonneg hv0 (by positivity)
    · have hnorm := StateCutoff.norm_lt_of_ne_zero (by positivity : 0<(n:ℝ)+1) hz
      change ‖StateCutoff.cutoff ((n:ℝ)+1) z*dG t z‖≤_
      rw [norm_mul,Real.norm_eq_abs]
      calc
        _≤1*‖dG t z‖ := mul_le_mul_of_nonneg_right (StateCutoff.abs_le_one _ _) (norm_nonneg _)
        _≤v t*(1+‖z‖) := by simpa only [one_mul] using (hv t ht).2 z
        _≤_ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hnorm.le) hv0
  · obtain ⟨M,hM0,hM⟩ := hs.norm_bound
    obtain ⟨L,hL0,hL⟩ := hs.fderiv.norm_bound
    exact ⟨M,L,B,fun t z => ⟨hM t z,hL t z,hDb t z⟩⟩

end SHE.LocalizedItoTest
