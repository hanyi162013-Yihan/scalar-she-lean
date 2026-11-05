module

public import SHE.TerminalItoFubini
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.TerminalItoAverageWitness
open Set Filter MeasureTheory PredictableL2
open scoped ENNReal NNReal
variable {Ω P C:Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- A genuinely joint bounded family of ORIGINAL scalar Ito integrals
remains an original integral after finite parameter averaging. The proof
uses the closed Hilbert range and scalar Fubini, so it does not assume
separability of the entire probability L2 space or a parameterized Ito map. -/
theorem bounded_average (ν:Measure P) [IsFiniteMeasure ν] (F:P×Ω→ℝ) (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀p ω,‖F (p,ω)‖≤B)
    (hrep:∀p,∃V:Process (E:=C) 𝓕 μ H,J.integral V=ᵐ[μ] fun ω=>F (p,ω)):
    ∃V:Process (E:=C) 𝓕 μ H,J.integral V=ᵐ[μ] fun ω=>∫p,F (p,ω) ∂ν:=by
  let g:=fun ω=>∫p,F (p,ω) ∂ν
  have hgm:Measurable g:=hF.stronglyMeasurable.integral_prod_left'.measurable
  have hgb(ω:Ω):‖g ω‖≤ν.real univ*B:=by
    simpa only [g,mul_comm] using
      (norm_integral_le_of_norm_le_const (μ:=ν) (Filter.Eventually.of_forall (fun p=>hb p ω)))
  have hg:MemLp g 2 μ:=MemLp.of_bound hgm.aestronglyMeasurable _ (Filter.Eventually.of_forall hgb)
  let G:Lp ℝ 2 μ:=hg.toLp g
  let K:Submodule ℝ (Lp ℝ 2 μ):=LinearMap.range J.integral.toLinearMap
  have hK:IsClosed (K:Set (Lp ℝ 2 μ)):=J.integral.isometry.isClosedEmbedding.isClosed_range
  have hKK:Kᗮᗮ=K:=by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact SetLike.coe_injective hK.closure_eq
  have hmem:G∈K:=by
    rw [←hKK]
    apply (Submodule.mem_orthogonal _ _).mpr
    intro Z hZ
    have hiZ:Integrable (fun ω=>Z ω) μ:=(Lp.memLp Z).integrable (by norm_num : (1:ENNReal)≤2)
    have hi:Integrable (fun z:P×Ω=>F z*Z z.2) (ν.prod μ):=by
      apply (((integrable_const B):Integrable (fun _:P=>B) ν).mul_prod hiZ.norm).mono'
        (hF.mul ((Lp.stronglyMeasurable Z).measurable.comp measurable_snd)).aestronglyMeasurable
      filter_upwards with z
      change ‖F z*Z z.2‖≤B*‖Z z.2‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z.1 z.2) (norm_nonneg _)
    have hs(p:P):(∫ω,F (p,ω)*Z ω ∂μ)=0:=by
      obtain ⟨V,hV⟩:=hrep p
      have hh:inner ℝ (J.integral V) Z=0:=(Submodule.mem_orthogonal K Z).mp hZ _ ⟨V,rfl⟩
      rw [L2.inner_def] at hh
      simpa only [RCLike.inner_apply,conj_trivial] using
        (integral_congr_ae (hV.mono (fun ω hω=>by rw [hω];simp only [RCLike.inner_apply,conj_trivial,mul_comm]))).symm.trans hh
    have hswi:Integrable (Function.uncurry (fun ω p=>F (p,ω)*Z ω)) (μ.prod ν):=by
      convert! hi.swap using 1
    have hh:inner ℝ G Z=0:=by
      rw [L2.inner_def]
      calc
        _=∫ω,g ω*Z ω ∂μ:=integral_congr_ae (hg.coeFn_toLp.mono (fun ω hω=>by
          change inner ℝ (G ω) (Z ω)=g ω*Z ω
          rw [hω];simp only [RCLike.inner_apply,conj_trivial,mul_comm]))
        _=∫ω,∫p,F (p,ω)*Z ω ∂ν ∂μ:=by simp only [g,integral_mul_const]
        _=∫p,∫ω,F (p,ω)*Z ω ∂μ ∂ν:=integral_integral_swap hswi
        _=0:=by simp only [hs,integral_zero]
    exact (inner_eq_zero_symm).mp hh
  obtain ⟨V,hV⟩:=hmem
  exact ⟨V,by rw [show J.integral V=G from hV];exact hg.coeFn_toLp⟩

end SHE.TerminalItoAverageWitness
