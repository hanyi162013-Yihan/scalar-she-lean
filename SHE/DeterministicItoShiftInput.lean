module
public import SHE.DeterministicItoShiftClock
public import SHE.DeterministicItoShiftMeasure
public import SHE.ProcessEnergy
public import SHE.PastItoAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
namespace SHE.DeterministicItoShift
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω]

theorem extend_forward[Zero C](v h:ℝ≥0)(f:ℝ≥0×Ω→C)(p:ℝ≥0×Ω)(hp:p.1∈Ioc 0 h):
    extend v h f (v+p.1,p.2)=f p:=by
  have hpR:(0:ℝ)<(p.1:ℝ):=by exact_mod_cast hp.1
  have hv:v<v+p.1:=by exact_mod_cast (show (v:ℝ)<(v:ℝ)+(p.1:ℝ) from by linarith)
  have hu:v+p.1≤v+h:=by gcongr;exact hp.2
  simp only [extend,ite_eq_left hv,ite_eq_left hu,relative,add_tsub_cancel_left]

theorem extend_off[Zero C](v h:ℝ≥0)(f:ℝ≥0×Ω→C)(p:ℝ≥0×Ω)
    (hp:p∉Ioc v (v+h)×ˢuniv):extend v h f p=0:=by
  unfold extend
  split_ifs with hv hu
  · exact False.elim (hp ⟨⟨hv,hu⟩,mem_univ _⟩)
  · rfl
  · rfl

variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[SFinite μ]
variable(H v h:ℝ≥0)(hvh:v+h≤H)
include hvh

/-- Actual AE local input identities transport to their physical
zero extensions; no choice of representatives is silently substituted. -/
theorem extend_ae {f g:ℝ≥0×Ω→C}
    (hf:@Measurable _ _ (filtration 𝓕 v).predictable _ f)
    (hg:@Measurable _ _ (filtration 𝓕 v).predictable _ g)
    (he:f=ᵐ[energyMeasure μ h] g):
    extend v h f=ᵐ[energyMeasure μ H] extend v h g:=by
  have hf':Measurable (extend v h f):=(extend_predictable 𝓕 v h hf).mono (predictable_le_product 𝓕) le_rfl
  have hg':Measurable (extend v h g):=(extend_predictable 𝓕 v h hg).mono (predictable_le_product 𝓕) le_rfl
  have hs:MeasurableSet (Ioc v (v+h)×ˢ(univ:Set Ω)):=measurableSet_Ioc.prod MeasurableSet.univ
  have hp:∀ᵐp∂energyMeasure μ h,
      extend v h f (v+p.1,p.2)=extend v h g (v+p.1,p.2):=by
    filter_upwards [he,(Measure.quasiMeasurePreserving_fst (μ:=timeMeasure h) (ν:=μ)).ae (timeMeasure_ae_mem h)] with p hp ht
    rw [extend_forward v h f p ht,extend_forward v h g p ht,hp]
  have hw:extend v h f=ᵐ[(energyMeasure μ H).restrict (Ioc v (v+h)×ˢuniv)] extend v h g:=by
    rw [←(product_translation μ H v h hvh).map_eq]
    exact (ae_map_iff (product_translation μ H v h hvh).measurable.aemeasurable
      (measurableSet_eq_fun hf' hg')).mpr hp
  filter_upwards [(ae_restrict_iff' hs).mp hw] with p hp
  by_cases hh:p∈Ioc v (v+h)×ˢuniv
  · exact hp hh
  · rw [extend_off v h f p hh,extend_off v h g p hh]

/-- Exact square energy of a physical zero extension. -/
theorem extend_energy {f:ℝ≥0×Ω→C}
    (hf:@Measurable _ _ (filtration 𝓕 v).predictable _ f):
    (∫⁻p,ENNReal.ofReal (‖extend v h f p‖^2) ∂energyMeasure μ H)=
      ∫⁻p,ENNReal.ofReal (‖f p‖^2) ∂energyMeasure μ h:=by
  have hm:Measurable (extend v h f):=(extend_predictable 𝓕 v h hf).mono (predictable_le_product 𝓕) le_rfl
  have hm2:Measurable (fun p=>ENNReal.ofReal (‖extend v h f p‖^2)):=
    ENNReal.measurable_ofReal.comp (hm.norm.pow_const 2)
  have hs:MeasurableSet (Ioc v (v+h)×ˢ(univ:Set Ω)):=measurableSet_Ioc.prod MeasurableSet.univ
  calc
    _=∫⁻p in Ioc v (v+h)×ˢuniv,ENNReal.ofReal (‖extend v h f p‖^2) ∂energyMeasure μ H:=by
      rw [←lintegral_indicator hs]
      apply lintegral_congr
      intro p
      by_cases hp:p∈Ioc v (v+h)×ˢuniv
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp,extend_off v h f p hp]
        simp
    _=∫⁻p,ENNReal.ofReal (‖extend v h f (v+p.1,p.2)‖^2) ∂energyMeasure μ h:=
      ((product_translation μ H v h hvh).lintegral_comp hm2).symm
    _=_:=by
      apply lintegral_congr_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ:=timeMeasure h) (ν:=μ)).ae (timeMeasure_ae_mem h)] with p hp
      rw [extend_forward v h f p hp]

/-- The SAME physical window extension is a genuine original
predictable L2 input, rather than an ambient measurable surrogate. -/
theorem input_memLp(f:Process (E:=C) (filtration 𝓕 v) μ h):
    @MemLp _ _ 𝓕.predictable _ _ (extend v h f) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=by
  have hf:@Measurable _ _ (filtration 𝓕 v).predictable _ f:=(Lp.stronglyMeasurable f).measurable
  have hp:StronglyMeasurable[𝓕.predictable] (extend v h f):=(extend_predictable 𝓕 v h hf).stronglyMeasurable
  have ha:MemLp f 2 (energyMeasure μ h):=memLp_of_memLp_trim (predictable_le_product (filtration 𝓕 v)) (Lp.memLp f)
  have hi:Integrable (fun p=>‖extend v h f p‖^2) (energyMeasure μ H):=by
    refine ⟨((hp.mono (predictable_le_product 𝓕)).norm.pow 2).aestronglyMeasurable,?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun p=>sq_nonneg ‖extend v h f p‖))).mpr
    rw [extend_energy 𝓕 μ H v h hvh hf]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun p=>sq_nonneg ‖f p‖))).mp ha.norm.integrable_sq.2
  have hm:MemLp (extend v h f) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm (hp.mono (predictable_le_product 𝓕)).aestronglyMeasurable).mpr hi
  exact (le_of_eq (eLpNorm_trim (predictable_le_product 𝓕) hp)).trans_lt hm

def input(f:Process (E:=C) (filtration 𝓕 v) μ h):Process (E:=C) 𝓕 μ H:=
  (input_memLp 𝓕 μ H v h hvh f).toLp (extend v h f)

theorem input_ae(f:Process (E:=C) (filtration 𝓕 v) μ h):
    input 𝓕 μ H v h hvh f=ᵐ[energyMeasure μ H] extend v h f:=
  ae_eq_of_ae_eq_trim (input_memLp 𝓕 μ H v h hvh f).coeFn_toLp

end SHE.DeterministicItoShift
