module

public import SHE.PastItoClosedRange
public import SHE.TerminalItoClosedLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.PastItoLimitWitness
open Set Filter MeasureTheory PredictableL2 PastItoInputs
open scoped ENNReal NNReal Topology
variable {Ω P C:Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H v:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- Strong original-Ito limits retain support after the SAME original
past time. This is closedness of the actual post-v input subspace. -/
theorem original_post_limit (input:ℕ→Process (E:=C) 𝓕 μ H) (F:ℕ→Ω→ℝ) (G:Ω→ℝ)
    (hg:MemLp G 2 μ)
    (hrep:∀n,J.integral (post 𝓕 μ H v (input n))=ᵐ[μ] F n)
    (hlim:Tendsto (fun n=>∫ω,‖F n ω-G ω‖^2 ∂μ) atTop (𝓝 0)):
    ∃V:Process (E:=C) 𝓕 μ H,J.integral (post 𝓕 μ H v V)=ᵐ[μ] G:=by
  let Z:Lp ℝ 2 μ:=hg.toLp G
  have ht:Tendsto (fun n=>J.integral (post 𝓕 μ H v (input n))) atTop (𝓝 Z):=by
    apply KernelEnergyCauchy.tendsto_of_energy_error _ Z
      (fun n=>ENNReal.ofReal (∫ω,‖F n ω-G ω‖^2 ∂μ))
      (by simpa only [Function.comp_def,ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim)
    intro n
    apply le_of_eq
    congr 1
    rw [realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (J.integral (post 𝓕 μ H v (input n))) Z,hrep n,hg.coeFn_toLp]
      with ω hs hf hgg
    rw [hs,Pi.sub_apply,hf,hgg]
  have hm:Z∈PastItoClosedRange.range 𝓕 μ H v J:=
    (PastItoClosedRange.range_closed 𝓕 μ H v J).mem_of_tendsto ht
      (Eventually.of_forall (fun n=>PastItoClosedRange.post_integral_mem 𝓕 μ H v J (input n)))
  obtain ⟨V,hV⟩:=hm
  refine ⟨V.1,?_⟩
  have hs:= (PastItoClosedRange.mem_supported 𝓕 μ H v V.1).mp V.2
  rw [hs]
  change J.integral V.1=Z at hV
  rw [hV]
  exact hg.coeFn_toLp

/-- Finite history averaging preserves the original post-v driver
support, without choosing a measurable family of stochastic inputs. -/
theorem bounded_post_average (ν:Measure P) [IsFiniteMeasure ν] (F:P×Ω→ℝ) (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀p ω,‖F (p,ω)‖≤B)
    (hrep:∀p,∃V:Process (E:=C) 𝓕 μ H,J.integral (post 𝓕 μ H v V)=ᵐ[μ] fun ω=>F (p,ω)):
    ∃V:Process (E:=C) 𝓕 μ H,J.integral (post 𝓕 μ H v V)=ᵐ[μ] fun ω=>∫p,F (p,ω) ∂ν:=by
  let g:=fun ω=>∫p,F (p,ω) ∂ν
  have hgm:Measurable g:=hF.stronglyMeasurable.integral_prod_left'.measurable
  have hgb(ω:Ω):‖g ω‖≤ν.real univ*B:=by
    simpa only [g,mul_comm] using
      (norm_integral_le_of_norm_le_const (μ:=ν) (Eventually.of_forall (fun p=>hb p ω)))
  have hg:MemLp g 2 μ:=MemLp.of_bound hgm.aestronglyMeasurable _ (Eventually.of_forall hgb)
  let G:Lp ℝ 2 μ:=hg.toLp g
  let K:=PastItoClosedRange.range 𝓕 μ H v J
  have hK:IsClosed (K:Set (Lp ℝ 2 μ)):=PastItoClosedRange.range_closed 𝓕 μ H v J
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
      have hh:inner ℝ (J.integral (post 𝓕 μ H v V)) Z=0:=
        (Submodule.mem_orthogonal K Z).mp hZ _ (PastItoClosedRange.post_integral_mem 𝓕 μ H v J V)
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
  refine ⟨V.1,?_⟩
  rw [(PastItoClosedRange.mem_supported 𝓕 μ H v V.1).mp V.2]
  change J.integral V.1=G at hV
  rw [hV]
  exact hg.coeFn_toLp

end SHE.PastItoLimitWitness
