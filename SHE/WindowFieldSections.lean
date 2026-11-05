module
public import SHE.SpatialTimeAE
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.WindowFieldSections
open Set MeasureTheory
variable {T Ω X:Type*}[MeasurableSpace T][MeasurableSpace Ω][MeasurableSpace X]
variable (ν:Measure T)(μ:Measure Ω)(ξ:Measure X)[SFinite ν][SFinite μ][SFinite ξ]

/-- A single measurable equality event transfers the true time/root/sample
window equality into spatial sections of the ORIGINAL product class. -/
theorem window {n:ℕ}(f g:Fin n→(T×Ω)×X→ℂ)(s:Set (T×Ω))(hs:MeasurableSet s)
    (hf:∀i,Measurable (f i))(hg:∀i,Measurable (g i))
    (h:∀ᵐt∂ν,∀ᵐx∂ξ,∀ᵐω∂μ,(t,ω)∈s→∀i,f i ((t,ω),x)=g i ((t,ω),x)):
    ∀ᵐx∂ξ,∀ᵐp∂ν.prod μ,p∈s→∀i,f i (p,x)=g i (p,x):=by
  classical
  let F:(T×Ω)×X→Fin n→ℂ:=fun z i=>if z.1∈s then f i z else 0
  let G:(T×Ω)×X→Fin n→ℂ:=fun z i=>if z.1∈s then g i z else 0
  have hmF:Measurable F:=measurable_pi_iff.mpr (fun i=>(hf i).ite (hs.preimage measurable_fst) measurable_const)
  have hmG:Measurable G:=measurable_pi_iff.mpr (fun i=>(hg i).ite (hs.preimage measurable_fst) measurable_const)
  have he:∀ᵐt∂ν,∀ᵐx∂ξ,∀ᵐω∂μ,F ((t,ω),x)=G ((t,ω),x):=by
    filter_upwards [h] with t ht
    filter_upwards [ht] with x hx
    filter_upwards [hx] with ω hω
    funext i
    by_cases hp:(t,ω)∈s
    · simpa only [F,G,if_pos hp] using hω hp i
    · simp only [F,G,if_neg hp]
  filter_upwards [SpatialTimeAE.root_energy ν μ ξ hmF hmG he] with x hx
  filter_upwards [hx] with p hp
  intro hs i
  exact by simpa only [F,G,if_pos hs] using congrFun hp i
end SHE.WindowFieldSections
