module
public import SHE.ConditionalInitialState
public import SHE.StandardTerminalIto
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ConditionalCanonicalItoLimit
open MeasureTheory ProbabilityTheory PredictableL2 Filter Topology
open scoped NNReal ENNReal

variable{Ω P X:Type*}[MeasurableSpace Ω][MeasurableSpace P][MeasurableSpace X]
variable[StandardBorelSpace X][Nonempty X]

/-- An actual original-sample limit of measurable canonical sums passes
to almost every genuine conditional future law. -/
theorem ae_limit (μ:Measure Ω)[IsFiniteMeasure μ]
    (history:Ω→P)(canonical:Ω→X)(hp:Measurable history)(hc:Measurable canonical)
    (s:ℕ→X→ℝ)(z:X→ℝ)(hs:∀n,Measurable (s n))(hz:Measurable z)
    (hlim:∀ᵐω∂μ,Tendsto (fun n=>s n (canonical ω)) atTop (𝓝 (z (canonical ω)))):
    ∀ᵐp∂μ.map history,∀ᵐx∂condDistrib canonical history μ p,
      Tendsto (fun n=>s n x) atTop (𝓝 (z x)):=by
  apply Measure.ae_ae_of_ae_compProd (μ:=μ.map history) (κ:=condDistrib canonical history μ)
    (p:=fun w:P×X=>Tendsto (fun n=>s n w.2) atTop (𝓝 (z w.2)))
  rw[compProd_map_condDistrib hp.aemeasurable hc.aemeasurable]
  exact (ae_map_iff (hp.prodMk hc).aemeasurable
    (measurableSet_tendsto_fun (fun n=>(hs n).comp measurable_snd)
      (hz.comp measurable_snd))).mpr hlim

variable{ι:Type*}[Countable ι]
/-- Countably many observed limits share one exceptional history event. -/
theorem ae_limits (μ:Measure Ω)[IsFiniteMeasure μ]
    (history:Ω→P)(canonical:Ω→X)(hp:Measurable history)(hc:Measurable canonical)
    (s:ι→ℕ→X→ℝ)(z:ι→X→ℝ)(hs:∀i n,Measurable (s i n))(hz:∀i,Measurable (z i))
    (hlim:∀i,∀ᵐω∂μ,Tendsto (fun n=>s i n (canonical ω)) atTop (𝓝 (z i (canonical ω)))):
    ∀ᵐp∂μ.map history,∀i,∀ᵐx∂condDistrib canonical history μ p,
      Tendsto (fun n=>s i n x) atTop (𝓝 (z i x)):=
  ae_all_iff.mpr (fun i=>ae_limit μ history canonical hp hc (s i) (z i) (hs i) (hz i) (hlim i))

section Identify
variable{Y C:Type*}[MeasurableSpace Y]
variable[NormedAddCommGroup C][NormedSpace ℝ C]

/- The limit of the SAME elementary scalar integrals is the integral
of the genuine L2 limit input. Isometry continuity supplies the limit;
the observed almost-sure limit supplies its identification. -/
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Y›)(ν:Measure Y)(h:ℝ≥0)

theorem identify (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 ν h)
    (f:Process (E:=C) 𝓕 ν h)(fn:ℕ→Process (E:=C) 𝓕 ν h)
    (s:ℕ→Y→ℝ)(z:Y→ℝ)
    (hin:Tendsto fn atTop (𝓝 f))
    (hcell:∀n,(fun y:Y=>(J.integral (fn n):Lp ℝ 2 ν) y)=ᵐ[ν] s n)
    (hlim:∀ᵐy∂ν,Tendsto (fun n=>s n y) atTop (𝓝 (z y))):
    z=ᵐ[ν] (fun y:Y=>(J.integral f:Lp ℝ 2 ν) y):=by
  have hJ:Tendsto (fun n=>(J.integral (fn n):Lp ℝ 2 ν)) atTop (𝓝 (J.integral f:Lp ℝ 2 ν)):=
    (J.integral.continuous.tendsto f).comp hin
  have hm:TendstoInMeasure ν (fun n=>(J.integral (fn n):Y→ℝ)) atTop (J.integral f):=
    tendstoInMeasure_of_tendsto_Lp (p:=2) (μ:=ν) hJ
  obtain ⟨ns,hns,hsub⟩:=hm.exists_seq_tendsto_ae
  have hcells:∀ᵐy∂ν,∀n,(J.integral (fn n):Lp ℝ 2 ν) y=s n y:=ae_all_iff.mpr hcell
  exact (hlim.and (hsub.and hcells)).mono (fun y hy=>by
    have he:(fun n=>(J.integral (fn (ns n)):Lp ℝ 2 ν) y)=(fun n=>s (ns n) y):=
      funext (fun n=>hy.2.2 (ns n))
    have hJy:=hy.2.1
    rw[he] at hJy
    exact tendsto_nhds_unique (hy.1.comp hns.tendsto_atTop) hJy)
end Identify

variable{C:Type*}[NormedAddCommGroup C][NormedSpace ℝ C]
/- Conditional integral identification for a countable observation
family on ONE history event. Finite-cell identities and conditional input
L2 convergence are explicit ordinary integral obligations; no conditional
SPDE equation or transition law is supplied as a premise. -/
section Conditional
variable (μ:Measure Ω)[IsFiniteMeasure μ]
    (history:Ω→P)(canonical:Ω→X)(hp:Measurable history)(hc:Measurable canonical)
    (s:ι→ℕ→X→ℝ)(z:ι→X→ℝ)(hs:∀i n,Measurable (s i n))(hz:∀i,Measurable (z i))
    (hlim:∀i,∀ᵐω∂μ,Tendsto (fun n=>s i n (canonical ω)) atTop (𝓝 (z i (canonical ω))))
    (h:ℝ≥0)(𝓕:P→Filtration ℝ≥0 ‹MeasurableSpace X›)
    (J:∀p,StandardTerminalIto (C:=C) (E:=ℝ) (𝓕 p) (condDistrib canonical history μ p) h)
    (f:∀p,ι→Process (E:=C) (𝓕 p) (condDistrib canonical history μ p) h)
    (fn:∀p,ι→ℕ→Process (E:=C) (𝓕 p) (condDistrib canonical history μ p) h)

include hp hc hs hz hlim in
theorem identify_conditional (hin:∀i,∀ᵐp∂μ.map history,Tendsto (fn p i) atTop (𝓝 (f p i)))
    (hcell:∀i n,∀ᵐp∂μ.map history,(fun x:X=>(J p).integral (fn p i n) x)=ᵐ[condDistrib canonical history μ p] s i n):
    ∀ᵐp∂μ.map history,∀i,z i=ᵐ[condDistrib canonical history μ p] (fun x:X=>(J p).integral (f p i) x):=by
  have hcellAll:∀ᵐp∂μ.map history,∀i n,
      (fun x:X=>(J p).integral (fn p i n) x)=ᵐ[condDistrib canonical history μ p] s i n:=
    ae_all_iff.mpr (fun i=>ae_all_iff.mpr (hcell i))
  filter_upwards[ae_limits μ history canonical hp hc s z hs hz hlim,
    ae_all_iff.mpr hin,hcellAll] with p hpLim hpIn hpCell
  intro i
  exact identify (𝓕 p) (condDistrib canonical history μ p) h (J p)
    (f p i) (fn p i) (s i) (z i) (hpIn i) (hpCell i) (hpLim i)
end Conditional
end SHE.ConditionalCanonicalItoLimit
