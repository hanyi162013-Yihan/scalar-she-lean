module
public import SHE.StandardItoParameterFubini
public import SHE.NullCompleteFiltration
public import SHE.StoppedItoInputs
public import SHE.PredictableTime
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω][NormedAddCommGroup C][InnerProductSpace ℝ C]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}{H:ℝ≥0}

/-- An explicit ordinary STOPPED parameterized-integral component of
accepted stochastic Fubini package 4. This property is an external
standard-input hypothesis, not a Lean theorem or a new axiom. It is
stronger than the earlier ambient-Borel-only parameter interface.

For a jointly predictable square-integrable generic kernel, the SAME
original J has a joint parameter/predictable stopped version, continuous
for almost every parameter/sample. The original deterministic-stop
identity holds for every stop on one parameter-AE event. The measure is
the specified SFinite parameter measure; no universally-all-parameter
version, SPDE, Gaussian profile or comparison conclusion is assumed. -/
def StandardItoStoppedParameterFubini
    (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H):Prop:=
  NullCompleteFiltration.ContainsNullSets 𝓕 μ→
  ∀(X:Type)[MeasurableSpace X](ν:Measure X)[SFinite ν]
    (K:X→Process (E:=C) 𝓕 μ H)(raw:X×(ℝ≥0×Ω)→C),
    StronglyMeasurable[(inferInstance:MeasurableSpace X).prod 𝓕.predictable] raw→
    (∀x,K x=ᵐ[energyMeasure μ H] fun p=>raw (x,p))→
    (∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞→
    ∃Y:X×(ℝ≥0×Ω)→ℝ,
      StronglyMeasurable[(inferInstance:MeasurableSpace X).prod 𝓕.predictable] Y ∧
      (∀ᵐx∂ν,∀q:ℝ≥0,(fun ω=>Y (x,(q,ω)))=ᵐ[μ]
        J.integral (StoppedItoInputs.stop 𝓕 μ H (q:ℝ) (K x))) ∧
      (∀ᵐx∂ν,∀ᵐω∂μ,Continuous (fun q=>Y (x,(q,ω))))

namespace StandardItoStoppedParameterFubini
variable [SFinite μ]

theorem stop_after_horizon (u:Process (E:=C) 𝓕 μ H):
    StoppedItoInputs.stop 𝓕 μ H ((H:ℝ)+1) u=u:=by
  have ht:∀ᵐp∂energyMeasure μ H,p.1≤H:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_fst measurable_const)).mpr
    filter_upwards [timeMeasure_ae_mem H] with t ht
    exact Filter.Eventually.of_forall (fun _=>ht.2)
  apply (processEmbedding 𝓕 μ H).injective
  apply Lp.ext
  filter_upwards [ambient_ae (energyMeasure μ H) (predictable_le_product 𝓕)
      (StoppedItoInputs.stop 𝓕 μ H ((H:ℝ)+1) u),
    ambient_ae (energyMeasure μ H) (predictable_le_product 𝓕) u,
    StoppedItoInputs.stop_ae 𝓕 μ H ((H:ℝ)+1) u,ht] with p hs hu hi ht
  change ambient (energyMeasure μ H) (predictable_le_product 𝓕)
    (StoppedItoInputs.stop 𝓕 μ H ((H:ℝ)+1) u) p=
    ambient (energyMeasure μ H) (predictable_le_product 𝓕) u p
  rw [hs,hu,hi,Set.indicator_of_mem]
  change (p.1:ℝ)<(H:ℝ)+1
  have ht':(p.1:ℝ)≤H:=by exact_mod_cast ht
  linarith

/-- The stronger ordinary stopped-version input implies the prior
ambient parameterized interface; the earlier weaker interface remains
unchanged. This implication is internally proved. -/
theorem ambient (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoStoppedParameterFubini J)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ):StandardItoParameterFubini J:=by
  intro X _ ν _ K raw hraw hK hfinite
  obtain ⟨Y,hY,hYa,hYc⟩:=hF hnull X ν K raw hraw hK hfinite
  let Y':X×Ω→ℝ:=fun z=>Y (z.1,(H+1,z.2))
  have hp:@Measurable (X×Ω) (X×(ℝ≥0×Ω)) _
      ((inferInstance:MeasurableSpace X).prod 𝓕.predictable)
      (fun z=>(z.1,(H+1,z.2))):=
    measurable_fst.prodMk ((measurable_const.prodMk measurable_snd).mono le_rfl (predictable_le_product 𝓕))
  refine ⟨Y',(hY.comp_measurable hp).measurable,?_⟩
  filter_upwards [hYa] with x hx
  simpa only [Y',show ((H+1:ℝ≥0):ℝ)=(H:ℝ)+1 from rfl,stop_after_horizon] using hx (H+1)
end StandardItoStoppedParameterFubini
end SHE
