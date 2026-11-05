module

public import SHE.GaussianShiftedReferenceMoments
public import SHE.GaussianScoreKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.GaussianKernelShiftedLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianIncrement GaussianScoreKernel
  GaussianCenteredLeafMoments GaussianReferenceLeafMoments
open scoped NNReal

/-- Genuine kernel Fubini with a positive integrable fiber bound. The
kernel and integrand may depend on exactly the same outer parameter. -/
theorem nonnegative_kernel_bound {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [SFinite μ] (κ : Kernel Ω Y) [IsSFiniteKernel κ]
    (f : Ω×Y → ℝ) (hf : Measurable f) (hpos : ∀ z,0≤f z)
    (J : Ω → ℝ) (hJ : Integrable J μ)
    (hi : ∀ ω,Integrable (fun y => f (ω,y)) (κ ω))
    (hb : ∀ ω,(∫ y,f (ω,y) ∂κ ω)≤J ω) :
    Integrable f (μ⊗ₘκ) ∧ (∫ z,f z ∂μ⊗ₘκ)≤∫ ω,J ω ∂μ := by
  have hm : Measurable (fun ω => ∫ y,f (ω,y) ∂κ ω) :=
    (hf.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  have hg : Integrable (fun ω => ∫ y,f (ω,y) ∂κ ω) μ :=
    hJ.mono' hm.aestronglyMeasurable (ae_of_all _ (fun ω => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => hpos (ω,y)))]
      exact hb ω))
  have hn : Integrable (fun ω => ∫ y,‖f (ω,y)‖ ∂κ ω) μ := by
    convert! hg using 1
    funext ω
    apply integral_congr_ae
    exact ae_of_all _ (fun y => Real.norm_of_nonneg (hpos (ω,y)))
  have hif : Integrable f (μ⊗ₘκ) :=
    (Measure.integrable_compProd_iff hf.aestronglyMeasurable).mpr ⟨ae_of_all _ hi,hn⟩
  refine ⟨hif,?_⟩
  rw [Measure.integral_compProd hif]
  exact integral_mono hg hJ hb

/-- A reduced Gaussian future increment may have a rank-varying law
coupled to the current state. Its rough leaf is still centered at the
FULL profile Gaussian baseline. Only the true current-mean displacement
moment appears; no independence or Gaussian law for the current state is
assumed. -/
theorem even_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (A : Ω → Matrix (Fin n) (Fin n) ℝ) (hA : Measurable A)
    (X : Ω×State n → ℝ) (hX : Measurable X)
    (v full : Ω → ℝ≥0) (hfull : Measurable full)
    (hLaw : ∀ ω,HasLaw (fun y => X (ω,y)) (gaussianReal 0 (v ω))
      (multivariateGaussian (0 : State n) (A ω)))
    (hv : ∀ ω,v ω≤full ω) (cap : ℝ≥0) (hcap : ∀ ω,full ω≤cap)
    (m referenceMean : Ω → ℝ) (hm : Measurable m) (hmref : Measurable referenceMean)
    (a : ℝ → ℝ) (ha : Measurable a) (M H β : ℝ) (hM : ∀ z,|a z|≤M)
    (hH : 0≤H) (hβ : 0≤β) (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (p : ℕ) (hiOffset : Integrable (fun ω => |m ω-referenceMean ω|^(((2*p:ℕ):ℝ)*β)) μ) :
    let f := fun z : Ω×State n =>
      |a (m z.1+X z)-GaussianProfile.gaussianAverage a (referenceMean z.1) (full z.1)|^(2*p)
    Integrable f (μ⊗ₘgaussianKernel A hA) ∧
      (∫ z,f z ∂μ⊗ₘgaussianKernel A hA) ≤ (2 : ℝ)^(2*p-1)*
        (H^(2*p)*(∫ ω,|m ω-referenceMean ω|^(((2*p:ℕ):ℝ)*β) ∂μ)+
          leafMomentConstant p β*(H*(cap:ℝ)^(β/2))^(2*p)) := by
  intro f
  let J := fun ω => (2 : ℝ)^(2*p-1)*
    (H^(2*p)*|m ω-referenceMean ω|^(((2*p:ℕ):ℝ)*β)+
      leafMomentConstant p β*(H*(cap:ℝ)^(β/2))^(2*p))
  have hf : Measurable f := by
    have hb : Measurable (fun ω => GaussianProfile.gaussianAverage a (referenceMean ω) (full ω)) :=
      (GaussianProfile.gaussianAverage_joint_measurable ha).comp
        (hmref.prodMk ((measurable_coe_nnreal_real.comp hfull)))
    exact (continuous_abs.measurable.comp ((ha.comp ((hm.comp measurable_fst).add hX)).sub
      (hb.comp measurable_fst))).pow_const _
  have hJ : Integrable J μ :=
    ((hiOffset.const_mul _).add (integrable_const _)).const_mul _
  have hleaf (ω : Ω) : Integrable (fun y => f (ω,y)) (multivariateGaussian (0 : State n) (A ω)) ∧
      (∫ y,f (ω,y) ∂multivariateGaussian (0 : State n) (A ω))≤J ω := by
    have hh := GaussianShiftedReferenceMoments.shifted_reference_even_moment
      (multivariateGaussian (0 : State n) (A ω)) (fun y => X (ω,y)) (fun _ => m ω)
      (hX.comp (measurable_const.prodMk measurable_id)) measurable_const (hLaw ω) (hv ω)
      a ha M H β hM hH hβ hholder (referenceMean ω) p (integrable_const _)
    refine ⟨hh.1,hh.2.trans ?_⟩
    have hvpow : (full ω:ℝ)^(β/2)≤(cap:ℝ)^(β/2) :=
      rpow_le_rpow (full ω).2 (by exact_mod_cast hcap ω) (by positivity)
    have hb := pow_le_pow_left₀ (mul_nonneg hH (rpow_nonneg (full ω).2 _))
      (mul_le_mul_of_nonneg_left hvpow hH) (2*p)
    have hc := mul_le_mul_of_nonneg_left hb (leafMomentConstant_nonneg p β)
    dsimp [J]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    convert! mul_le_mul_of_nonneg_left (add_le_add le_rfl hc)
      (show 0≤(2:ℝ)^(2*p-1) by positivity) using 1
  have hh := nonnegative_kernel_bound μ (gaussianKernel A hA) f hf (fun _ => by positivity)
    J hJ (fun ω => (hleaf ω).1) (fun ω => (hleaf ω).2)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  dsimp [J]
  rw [integral_const_mul,integral_add (hiOffset.const_mul _) (integrable_const _),integral_const_mul]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

end SHE.GaussianKernelShiftedLeaf
