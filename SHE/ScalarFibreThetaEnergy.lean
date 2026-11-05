module
public import SHE.ScalarFibreRMS
public import SHE.SectionFirstMoment
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.ScalarFibreThetaEnergy
open Set MeasureTheory Real
variable {Ω Θ X:Type*}[MeasurableSpace Ω][MeasurableSpace Θ][MeasurableSpace X]

/-- Actual joint sample/spatial energies give genuine joint theta/spatial
square integrability of SAMPLE RMS, before pointwise theta Minkowski.
The output measure need not be a probability. -/
theorem joint (μ:Measure Ω)[SFinite μ](ν:Measure X)[SFinite ν]
    (τ:Measure Θ)[IsProbabilityMeasure τ](F:Ω×(Θ×X)→ℝ)(hF:Measurable F)(B:ℝ)
    (hs:∀ᵐθ∂τ,Integrable (fun z:Ω×X=>|F (z.1,(θ,z.2))|^2) (μ.prod ν) ∧
      (∫z:Ω×X,|F (z.1,(θ,z.2))|^2 ∂μ.prod ν)≤B):
    let G:=ScalarFibreRMS.rms μ F
    Integrable (fun z:Θ×X=>G z^2) (τ.prod ν) ∧
      (∫z:Θ×X,G z^2 ∂τ.prod ν)≤B:=by
  intro G
  have hG:Measurable G:=ScalarFibreRMS.measurable μ F hF
  have hsec:∀ᵐθ∂τ,Integrable (fun x=>G (θ,x)^2) ν ∧
      (∫x,G (θ,x)^2 ∂ν)≤B:=by
    filter_upwards [hs] with θ hθ
    have hm:Measurable (fun z:Ω×X=>F (z.1,(θ,z.2))):=
      hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have he:=ScalarFibreRMS.memLp_energy μ ν _ hm hθ.1
    refine ⟨(memLp_two_iff_integrable_sq he.1.aestronglyMeasurable).mp he.1,?_⟩
    have heq:=he.2
    rw [ProfileL2.normTwo_sq] at heq
    exact heq.le.trans hθ.2
  have hjs:=SectionFirstMoment.joint_integrable ν τ
    (fun z:X×Θ=>G (z.2,z.1)^2) ((hG.comp measurable_swap).pow_const 2)
    (fun _=>B) (integrable_const B) (hsec.mono (fun θ hθ=>⟨hθ.1,by
      have heq:(fun x:X=>|G (θ,x)^2|)=(fun x=>G (θ,x)^2):=
        funext (fun x=>abs_of_nonneg (sq_nonneg (G (θ,x))))
      rw [heq]
      exact hθ.2⟩))
  have hj:Integrable (fun z:Θ×X=>G z^2) (τ.prod ν):=hjs.1.swap
  refine ⟨hj,?_⟩
  rw [integral_prod _ hj]
  have hb:=integral_mono_ae hj.integral_prod_left (integrable_const B) (hsec.mono (fun _ h=>h.2))
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hb
end SHE.ScalarFibreThetaEnergy
