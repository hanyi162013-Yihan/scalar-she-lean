module

public import SHE.HilbertFiniteAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.HilbertParameterAverage
open Set Filter MeasureTheory Real
variable {Ω P T E : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace T]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Correct old-time/current-time ordering: integrate the old-parameter
RMS bound first, square it, and only then integrate current time. The
unaveraged square need not be jointly integrable in the old parameters. -/
theorem time_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure P) [IsFiniteMeasure ν] (τ : Measure T) [SFinite τ]
    (F : P × (T × Ω) → E) (hF : Measurable F)
    (B : T × P → ℝ) (hBm : Measurable B) (hB0 : ∀ t p,0 ≤ B (t,p))
    (hBi : ∀ᵐ t ∂τ,Integrable (fun p => B (t,p)) ν)
    (hBt : Integrable (fun t => (∫ p,B (t,p) ∂ν)^2) τ)
    (hi : ∀ᵐ t ∂τ,∀ᵐ p ∂ν,Integrable (fun ω => ‖F (p,(t,ω))‖^2) μ)
    (hb : ∀ᵐ t ∂τ,∀ᵐ p ∂ν,(∫ ω,‖F (p,(t,ω))‖^2 ∂μ) ≤ B (t,p)^2) :
    Integrable (fun z : T × Ω => ‖∫ p,F (p,z) ∂ν‖^2) (τ.prod μ) ∧
      (∫ z : T × Ω,‖∫ p,F (p,z) ∂ν‖^2 ∂τ.prod μ) ≤
        ∫ t,(∫ p,B (t,p) ∂ν)^2 ∂τ := by
  have hG : Measurable (fun z : T × Ω => ‖∫ p,F (p,z) ∂ν‖^2) :=
    hF.stronglyMeasurable.integral_prod_left'.measurable.norm.pow_const 2
  have hsections : ∀ᵐ t ∂τ,Integrable (fun ω => ‖∫ p,F (p,(t,ω)) ∂ν‖^2) μ ∧
      (∫ ω,‖∫ p,F (p,(t,ω)) ∂ν‖^2 ∂μ) ≤ (∫ p,B (t,p) ∂ν)^2 := by
    filter_upwards [hBi,hi,hb] with t ht hi hb
    have hFt : Measurable (fun z : P × Ω => F (z.1,(t,z.2))) :=
      hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    exact (finite_energy μ ν _ hFt _ (hBm.comp (measurable_const.prodMk measurable_id))
      ht (hB0 t) hi hb).2
  have hM : Measurable (fun t => ∫ ω,‖∫ p,F (p,(t,ω)) ∂ν‖^2 ∂μ) :=
    (hG.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable
  have hIt : Integrable (fun t => ∫ ω,‖∫ p,F (p,(t,ω)) ∂ν‖^2 ∂μ) τ := by
    apply hBt.mono' hM.aestronglyMeasurable
    filter_upwards [hsections] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact ht.2
  have hJoint : Integrable (fun z : T × Ω => ‖∫ p,F (p,z) ∂ν‖^2) (τ.prod μ) := by
    apply (integrable_prod_iff hG.aestronglyMeasurable).mpr
    refine ⟨hsections.mono (fun _ h => h.1),?_⟩
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hIt
  refine ⟨hJoint,?_⟩
  rw [integral_prod _ hJoint]
  exact integral_mono_ae hIt hBt (hsections.mono (fun _ h => h.2))

end SHE.HilbertParameterAverage
