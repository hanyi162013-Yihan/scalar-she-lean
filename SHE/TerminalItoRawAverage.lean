module

public import SHE.TerminalItoAverageWitness
public import SHE.HilbertParameterAverage
public import SHE.PastItoAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000

namespace SHE.TerminalItoRawAverage
open MeasureTheory Set PredictableL2
open scoped ENNReal NNReal
variable {Ω P C:Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

theorem process_inner (u w:Process (E:=C) 𝓕 μ H):
    inner ℝ u w=∫z,inner ℝ (u z) (w z) ∂energyMeasure μ H:=by
  rw [L2.inner_def]
  exact (integral_trim (μ:=energyMeasure μ H) (predictable_le_product 𝓕)
    ((Lp.stronglyMeasurable u).inner (Lp.stronglyMeasurable w))).symm

/-- Finite averaging identifies the actual predictable input, not merely
an existential terminal integral. Weak Hilbert pairings avoid any
separability assumption on the probability L2 space. -/
theorem bounded_average (ν:Measure P) [IsFiniteMeasure ν]
    (raw:P×(ℝ≥0×Ω)→C)
    (hm:@Measurable (P×(ℝ≥0×Ω)) C
      ((inferInstance:MeasurableSpace P).prod 𝓕.predictable) inferInstance raw)
    {D:ℝ} (hD:0≤D) (hd:∀p z,‖raw (p,z)‖≤D)
    (F:P×Ω→ℝ) (hF:Measurable F) {B:ℝ} (hB:0≤B) (hb:∀p ω,‖F (p,ω)‖≤B)
    (hrep:∀p,∃input:Process (E:=C) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>raw (p,z)) ∧
      J.integral input=ᵐ[μ] fun ω=>F (p,ω)):
    ∃input:Process (E:=C) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,raw (p,z) ∂ν) ∧
      J.integral input=ᵐ[μ] fun ω=>∫p,F (p,ω) ∂ν:=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  have hmap:@Measurable (P×(ℝ≥0×Ω)) (P×(ℝ≥0×Ω)) inferInstance
      ((inferInstance:MeasurableSpace P).prod 𝓕.predictable) id:=
    measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
  have hraw:Measurable raw:=hm.comp hmap
  let g:=fun z:ℝ≥0×Ω=>∫p,raw (p,z) ∂ν
  have hgm:StronglyMeasurable[𝓕.predictable] g:=
    HilbertParameterAverage.average_predictable 𝓕 ν raw hm
  have hgb(z:ℝ≥0×Ω):‖g z‖≤ν.real univ*D:=by
    simpa only [g,mul_comm] using
      norm_integral_le_of_norm_le_const (μ:=ν) (Filter.Eventually.of_forall (fun p=>hd p z))
  have hg:@MemLp (ℝ≥0×Ω) C 𝓕.predictable _ _ g 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=
    MemLp.of_bound hgm.aestronglyMeasurable _ (Filter.Eventually.of_forall hgb)
  let W:Process (E:=C) 𝓕 μ H:=hg.toLp g
  have hW:W=ᵐ[energyMeasure μ H] g:=ae_eq_of_ae_eq_trim hg.coeFn_toLp
  obtain ⟨V,hV⟩:=TerminalItoAverageWitness.bounded_average 𝓕 μ H J ν F hF hB hb
    (fun p=>by obtain ⟨u,hu,hi⟩:=hrep p;exact ⟨u,hi⟩)
  have hpair(U:Process (E:=C) 𝓕 μ H):inner ℝ V U=inner ℝ W U:=by
    have hiU:Integrable (fun z=>U z) (energyMeasure μ H):=
      (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp U)).integrable (by norm_num)
    have hiJU:Integrable (fun ω=>J.integral U ω) μ:=(Lp.memLp (J.integral U)).integrable (by norm_num)
    have hUi:Measurable (fun z=>U z):=(Lp.stronglyMeasurable U).measurable.mono
      (predictable_le_product 𝓕) le_rfl
    have hiRaw:Integrable (fun z:P×(ℝ≥0×Ω)=>inner ℝ (raw z) (U z.2))
        (ν.prod (energyMeasure μ H)):=by
      apply (((integrable_const D):Integrable (fun _:P=>D) ν).mul_prod hiU.norm).mono'
        (hraw.stronglyMeasurable.inner (hUi.comp measurable_snd).stronglyMeasurable).aestronglyMeasurable
      filter_upwards with z
      exact (norm_inner_le_norm (raw z) (U z.2)).trans
        (mul_le_mul_of_nonneg_right (hd z.1 z.2) (norm_nonneg _))
    have hiF:Integrable (fun z:P×Ω=>F z*J.integral U z.2) (ν.prod μ):=by
      apply (((integrable_const B):Integrable (fun _:P=>B) ν).mul_prod hiJU.norm).mono'
        (hF.mul ((Lp.stronglyMeasurable (J.integral U)).measurable.comp measurable_snd)).aestronglyMeasurable
      filter_upwards with z
      change ‖F z*J.integral U z.2‖≤B*‖J.integral U z.2‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z.1 z.2) (norm_nonneg _)
    have hs(p:P):(∫ω,F (p,ω)*J.integral U ω ∂μ)=
        ∫z,inner ℝ (raw (p,z)) (U z) ∂energyMeasure μ H:=by
      obtain ⟨u,hu,hi⟩:=hrep p
      have hh:=J.integral.inner_map_map u U
      rw [L2.inner_def,process_inner] at hh
      calc
        _=∫ω,inner ℝ (J.integral u ω) (J.integral U ω) ∂μ:=by
          apply integral_congr_ae
          filter_upwards [hi] with ω hω
          rw [hω]
          simp only [RCLike.inner_apply,conj_trivial,mul_comm]
        _=∫z,inner ℝ (u z) (U z) ∂energyMeasure μ H:=hh
        _=_:=integral_congr_ae (hu.mono (fun z hz=>by change inner ℝ (u z) (U z)=_; rw [hz]))
    rw [←J.integral.inner_map_map V U,L2.inner_def,process_inner 𝓕 μ H W U]
    calc
      _=∫ω,(∫p,F (p,ω) ∂ν)*J.integral U ω ∂μ:=by
        apply integral_congr_ae
        filter_upwards [hV] with ω hω
        rw [hω]
        simp only [RCLike.inner_apply,conj_trivial,mul_comm]
      _=∫ω,∫p,F (p,ω)*J.integral U ω ∂ν ∂μ:=by simp only [integral_mul_const]
      _=∫p,∫ω,F (p,ω)*J.integral U ω ∂μ ∂ν:=by
        exact integral_integral_swap (by convert! hiF.swap using 1)
      _=∫p,∫z,inner ℝ (raw (p,z)) (U z) ∂energyMeasure μ H ∂ν:=by
        apply integral_congr_ae;exact Filter.Eventually.of_forall hs
      _=∫z,∫p,inner ℝ (raw (p,z)) (U z) ∂ν ∂energyMeasure μ H:=
        integral_integral_swap hiRaw
      _=∫z,inner ℝ (g z) (U z) ∂energyMeasure μ H:=by
        apply integral_congr_ae
        filter_upwards with z
        have hp:Integrable (fun p=>raw (p,z)) ν:=Integrable.of_bound
          (hraw.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable D
          (Filter.Eventually.of_forall (fun p=>hd p z))
        calc
          _=∫p,inner ℝ (U z) (raw (p,z)) ∂ν:=by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun p=>real_inner_comm _ _)
          _=inner ℝ (U z) (g z):=integral_inner hp _
          _=inner ℝ (g z) (U z):=real_inner_comm _ _
      _=_:=integral_congr_ae (hW.mono (fun z hz=>by change inner ℝ (g z) (U z)=inner ℝ (W z) (U z); rw [hz]))
  have heq:V=W:=by
    have hh:=hpair (V-W)
    have hz:inner ℝ (V-W) (V-W)=0:=by rw [inner_sub_left,hh];simp
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  exact ⟨W,hW,by simpa only [heq] using hV⟩

end SHE.TerminalItoRawAverage
