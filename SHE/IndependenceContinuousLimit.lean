module
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SHE.IndependenceContinuousLimit
open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped Topology
variable{Ω E F:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E]
variable[SecondCountableTopology E][CompleteSpace E]
variable[NormedAddCommGroup F][NormedSpace ℝ F][MeasurableSpace F][BorelSpace F]
variable[SecondCountableTopology F][CompleteSpace F]
variable(μ:Measure Ω)[IsFiniteMeasure μ]

private theorem bounded_test(X:ℕ→Ω→E) (Y:Ω→E)
    (hX:∀n,AEMeasurable (X n) μ) (hY:AEMeasurable Y μ)
    (hlim:∀ᵐω∂μ,Tendsto (fun n=>X n ω) atTop (𝓝 (Y ω)))
    (g:E →ᵇ ℂ):
    Tendsto (fun n=>∫ω,g (X n ω)∂μ) atTop (𝓝 (∫ω,g (Y ω)∂μ)):=by
  apply tendsto_integral_of_dominated_convergence (fun _:Ω=>‖g‖)
  · intro n
    exact (g.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun ω=>g.norm_coe_le_norm (X n ω))
  · filter_upwards[hlim] with ω hω
    exact g.continuous.continuousAt.tendsto.comp hω

private theorem char_limit(X:ℕ→Ω→E) (Y:Ω→E)
    (hX:∀n,AEMeasurable (X n) μ) (hY:AEMeasurable Y μ)
    (hlim:∀ᵐω∂μ,Tendsto (fun n=>X n ω) atTop (𝓝 (Y ω)))
    (L:StrongDual ℝ E):
    Tendsto (fun n=>charFunDual (μ.map (X n)) L) atTop (𝓝 (charFunDual (μ.map Y) L)):=by
  have hh:=bounded_test μ X Y hX hY hlim (probCharDual L)
  have he(n:ℕ):charFunDual (μ.map (X n)) L=∫ω,probCharDual L (X n ω)∂μ:=
    integral_map (hX n) (probCharDual L).continuous.aestronglyMeasurable
  have hy:charFunDual (μ.map Y) L=∫ω,probCharDual L (Y ω)∂μ:=
    integral_map hY (probCharDual L).continuous.aestronglyMeasurable
  simpa only[he,hy] using hh

/-- Independence is closed under AE pointwise convergence of actual
Banach-valued variables. Bounded characteristic tests give the limit;
no moment or independence limit premise is assumed. -/
theorem independent(X:ℕ→Ω→E) (Y:ℕ→Ω→F) (x:Ω→E) (y:Ω→F)
    (hX:∀n,AEMeasurable (X n) μ) (hY:∀n,AEMeasurable (Y n) μ)
    (hx:AEMeasurable x μ) (hy:AEMeasurable y μ)
    (hxl:∀ᵐω∂μ,Tendsto (fun n=>X n ω) atTop (𝓝 (x ω)))
    (hyl:∀ᵐω∂μ,Tendsto (fun n=>Y n ω) atTop (𝓝 (y ω)))
    (hi:∀n,IndepFun (X n) (Y n) μ):IndepFun x y μ:=by
  apply (indepFun_iff_charFunDual_prod hx hy).mpr
  intro L
  have hpl:∀ᵐω∂μ,Tendsto (fun n=>(X n ω,Y n ω)) atTop (𝓝 (x ω,y ω)):=by
    filter_upwards[hxl,hyl] with ω hx hy
    exact hx.prodMk_nhds hy
  have hp:=char_limit μ (fun n ω=>(X n ω,Y n ω)) (fun ω=>(x ω,y ω))
    (fun n=>(hX n).prodMk (hY n)) (hx.prodMk hy) hpl L
  have hl:=(char_limit μ X x hX hx hxl (L.comp (.inl ℝ E F))).mul
    (char_limit μ Y y hY hy hyl (L.comp (.inr ℝ E F)))
  apply tendsto_nhds_unique hp
  exact hl.congr' (Eventually.of_forall (fun n=>
    ((indepFun_iff_charFunDual_prod (hX n) (hY n)).mp (hi n) L).symm))
end SHE.IndependenceContinuousLimit
