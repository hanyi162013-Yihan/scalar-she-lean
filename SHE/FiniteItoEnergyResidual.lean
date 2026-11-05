module

public import SHE.FiniteItoRowEnergy
public import SHE.FiniteItoResidualSections
public import SHE.LocalizedItoTest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.FiniteItoEnergyResidual
open Set MeasureTheory PredictableL2 GaussianItoTest GaussianTaylorAverage Filter Topology
open scoped NNReal ENNReal
variable {Ω X C : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable {n : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State n) (hY : ∀ ω,Continuous (fun t=>Y (t,ω)))
variable (R : Fin n→Process (E:=C) 𝓕 μ H)
variable (v c : ℝ≥0) (hvc : v≤c) (hcH : c≤H)
variable (G dG : X→ℝ→WordRecursion.State n→ℝ)
local notation "D" => StandardFiniteIto.rowCovariance 𝓕 μ H R

include hY hvc hcH in
/-- Actual predictable L² energy discharges random-reference residual
domination even for singular heat endpoint rows. No bounded-row premise
is required. -/
theorem continuous_residual (hreg : ∀ x,LocalizedItoTest.SmoothTimeTest v c (G x) (dG x))
    (hGp : ∀ t,Continuous (fun p : X×WordRecursion.State n=>G p.1 t p.2))
    (hHp : ∀ t,Continuous (fun p : X×WordRecursion.State n=>GaussianTaylor.hessian (G p.1 t) p.2))
    (hdGp : ∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (c:ℝ)),Continuous (fun p : X×WordRecursion.State n=>dG p.1 t p.2))
    (B : ℝ) (hB0 : 0≤B) (hB : ∀ x t z,‖GaussianTaylor.hessian (G x t) z‖≤B)
    (m : ℝ→ℝ) (hm : IntervalIntegrable m volume v c)
    (hm0 : ∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (c:ℝ)),0≤m t)
    (hmb : ∀ x,∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (c:ℝ)),∀ z,‖dG x t z‖≤m t*(1+‖z‖)) :
    ∀ᵐ ω∂μ,Continuous (fun x=>FiniteItoParameterResidual.residual Y D v c G dG x ω) := by
  have hvc' : (v:ℝ)≤(c:ℝ):=by exact_mod_cast hvc
  filter_upwards [FiniteItoRowEnergy.density_integrable 𝓕 μ H R v c v.2 hvc'
    (by exact_mod_cast hcH)] with ω hω
  have hp : Continuous (fun t:ℝ=>Y (t.toNNReal,ω)) := (hY ω).comp continuous_real_toNNReal
  obtain ⟨Q,hQ⟩:=(isCompact_Icc : IsCompact (Icc (v:ℝ) (c:ℝ))).exists_bound_of_continuousOn hp.continuousOn
  have hQ0 : 0≤Q := (norm_nonneg _).trans (hQ v ⟨le_rfl,hvc'⟩)
  let A := fun t:ℝ=>(1/2:ℝ)*(n:ℝ)^2*FiniteItoRowEnergy.density 𝓕 μ H R ω t*B
  apply FiniteItoResidualSections.continuous_residual Y D v c G dG hvc' hGp hHp hdGp ω
    (fun t=>m t*(1+Q)+A t) ((hm.mul_const _).add
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hvc').mpr ((hω.const_mul _).mul_const B)))
  · intro x
    have hpath := (hY ω).comp continuous_real_toNNReal
    have hmap : Measurable (fun t:ℝ=>(t,Y (t.toNNReal,ω))):=measurable_id.prodMk hpath.measurable
    have hd := (hreg x).derivative_measurable.comp hmap
    have hhc := ParameterSmoothContinuity.continuous_hessian (G x) (hreg x).continuous (hreg x).uniformSmooth
    have hess := hhc.comp (continuous_id.prodMk hpath)
    apply Measurable.aestronglyMeasurable
    apply hd.add
    apply Measurable.const_mul
    unfold covarianceAction
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact (FiniteItoCovarianceBounds.entry_measurable 𝓕 μ H R ω i j).mul
      (((hess.clm_apply continuous_const).clm_apply continuous_const).measurable)
  · intro x
    filter_upwards [hmb x,hm0,ae_restrict_mem measurableSet_Ioc] with t hmt hm0 htm
    have hs:=FiniteItoRowEnergy.density_nonneg 𝓕 μ H R ω t
    have ht:=FiniteItoRowEnergy.entry_bound 𝓕 μ H R ω t
    have hb:=GaussianItoTest.action_entry_bound (D ω t)
      (GaussianTaylor.hessian (G x t) (Y (t.toNNReal,ω))) hs ht
    have hh:=hB x t (Y (t.toNNReal,ω))
    change ‖dG x t (Y (t.toNNReal,ω))+(1/2:ℝ)*covarianceAction (D ω t)
      (GaussianTaylor.hessian (G x t) (Y (t.toNNReal,ω)))‖≤m t*(1+Q)+A t
    apply (norm_add_le _ _).trans
    apply add_le_add ((hmt _).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hQ t ⟨htm.1.le,htm.2⟩)) hm0))
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hmul := mul_le_mul_of_nonneg_left
      (hb.trans (mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg _) hs))) (by norm_num : (0:ℝ)≤1/2)
    simpa only [A,mul_assoc] using hmul

end SHE.FiniteItoEnergyResidual
