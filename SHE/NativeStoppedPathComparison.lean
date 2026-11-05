module
public import SHE.NativePathLawComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.NativeStoppedPathComparison
open MeasureTheory Set
open scoped NNReal ENNReal BoundedContinuousFunction
variable {Ω E:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (H:ℝ≥0)
local instance :Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance :MeasurableSpace (Lp E 2 (SHE.timeMeasure (H:ℝ))):=borel _
local instance :BorelSpace (Lp E 2 (SHE.timeMeasure (H:ℝ))):=⟨rfl⟩

theorem integrated_eq(U V:ℝ≥0→Ω→E)
    (hc:∀ω,Continuous (fun t=>U t ω))(hd:∀ω,Continuous (fun t=>V t ω))
    (ω:Ω)(he:∀t:ℝ≥0,t≤H→U t ω=V t ω):
    NativeContinuousPath.integrated H U hc ω=NativeContinuousPath.integrated H V hd ω:=by
  apply congrArg (ContinuousMap.toLp (E:=E) 2 (SHE.timeMeasure (H:ℝ)) ℝ)
  apply ContinuousMap.ext
  intro t
  exact he t.val.toNNReal ((Real.toNNReal_le_iff_le_coe).mpr t.property.2)

/-- Actual continuous versions need only agree almost surely before
the cap exit. Equivalence of the changed measure carries that null
set to Q; no pointwise canonical agreement on all samples is assumed. -/
theorem bound(μ Q:Measure Ω)(hQμ:Q≪μ){B:Set Ω}(hB:MeasurableSet B)(cost:ℝ)
    (hcompare:∀(f g:Ω→ℝ)(A:ℝ),AEStronglyMeasurable f μ→AEStronglyMeasurable g μ→
      0≤A→(∀ω,|f ω|≤A)→(∀ω,|g ω|≤A)→
      (∀ω,ω∉B→f ω=g ω)→
      |(∫ω,f ω ∂μ)-(∫ω,g ω ∂Q)|≤2*A*(Real.sqrt cost+cost))
    (U V:ℝ≥0→Ω→E)
    (hc:∀ω,Continuous (fun t=>U t ω))(hd:∀ω,Continuous (fun t=>V t ω))
    (hU:Measurable (Function.uncurry U))(hV:Measurable (Function.uncurry V))
    (hagree:∀ᵐω∂μ,ω∉B→∀t:ℝ≥0,t≤H→U t ω=V t ω)
    (canonical:ProbabilityMeasure (Lp E 2 (SHE.timeMeasure (H:ℝ))))
    (hcanonical:(canonical:Measure _)=Q.map (NativeContinuousPath.integrated H V hd))
    (f:Lp E 2 (SHE.timeMeasure (H:ℝ))→ᵇℝ):
    |(∫ω,f (NativeContinuousPath.integrated H U hc ω) ∂μ)-(∫x,f x ∂canonical)|≤
      2*‖f‖*(Real.sqrt cost+cost):=by
  classical
  let F:Ω→ℝ:=fun ω=>f (NativeContinuousPath.integrated H U hc ω)
  let G:Ω→ℝ:=fun ω=>f (NativeContinuousPath.integrated H V hd ω)
  let G':Ω→ℝ:=B.piecewise G F
  have hmF:Measurable F:=f.continuous.measurable.comp (NativeContinuousPath.measurable_integrated H U hc hU)
  have hmG:Measurable G:=f.continuous.measurable.comp (NativeContinuousPath.measurable_integrated H V hd hV)
  have hmG':Measurable G':=Measurable.piecewise hB hmG hmF
  have hbf:∀x,|f x|≤‖f‖:=fun x=>by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have he:G'=ᵐ[μ] G:=by
    filter_upwards [hagree] with ω hω
    by_cases hb:ω∈B
    · simp only [G',Set.piecewise,if_pos hb]
    · have hv:=integrated_eq H U V hc hd ω (hω hb)
      simp only [G',Set.piecewise,if_neg hb,F,G,hv]
  have hh:=hcompare F G' ‖f‖ hmF.aestronglyMeasurable hmG'.aestronglyMeasurable
    (norm_nonneg f) (fun ω=>hbf _) (fun ω=>by
      by_cases hb:ω∈B
      · simpa only [G',Set.piecewise,if_pos hb,G] using hbf (NativeContinuousPath.integrated H V hd ω)
      · simpa only [G',Set.piecewise,if_neg hb,F] using hbf (NativeContinuousPath.integrated H U hc ω))
    (fun ω hb=>by simp only [G',Set.piecewise,if_neg hb])
  have hi:(∫ω,G' ω ∂Q)=∫ω,G ω ∂Q:=integral_congr_ae (hQμ.ae_le he)
  rw [hi] at hh
  rw [hcanonical,integral_map (NativeContinuousPath.measurable_integrated H V hd hV).aemeasurable
    f.continuous.aestronglyMeasurable]
  exact hh

end SHE.NativeStoppedPathComparison
