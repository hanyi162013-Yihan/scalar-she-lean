module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.FiniteJointProbabilityLimit
open MeasureTheory Filter
open scoped Topology
variable {Ω E F G:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsFiniteMeasure μ]
variable [NormedAddCommGroup E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable [NormedAddCommGroup F][MeasurableSpace F][BorelSpace F][SecondCountableTopology F]
variable [NormedAddCommGroup G][MeasurableSpace G][BorelSpace G][SecondCountableTopology G]

/-- Finite joint convergence preserves all dependent coordinates. -/
theorem prod (f:ℕ→Ω→E)(g:ℕ→Ω→F)(X:Ω→E)(Y:Ω→F)
    (hf:∀n,AEStronglyMeasurable (f n) μ)(hg:∀n,AEStronglyMeasurable (g n) μ)
    (hX:TendstoInMeasure μ f atTop X)(hY:TendstoInMeasure μ g atTop Y):
    TendstoInMeasure μ (fun n ω=>(f n ω,g n ω)) atTop (fun ω=>(X ω,Y ω)):=by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n=>(hf n).prodMk (hg n))).mpr
  intro ns hns
  obtain ⟨ms,hms,hf'⟩:=(hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks,hks,hg'⟩:=(hY.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks,hms.comp hks,?_⟩
  filter_upwards [hf',hg'] with ω hf' hg'
  exact (hf'.comp hks.tendsto_atTop).prodMk_nhds hg'

/-- Ordinary continuous maps preserve actual probability limits. -/
theorem continuous_map(f:ℕ→Ω→E)(X:Ω→E)(hf:∀n,AEStronglyMeasurable (f n) μ)
    (hX:TendstoInMeasure μ f atTop X)(φ:E→F)(hφ:Continuous φ):
    TendstoInMeasure μ (fun n ω=>φ (f n ω)) atTop (fun ω=>φ (X ω)):=by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n=>hφ.comp_aestronglyMeasurable (hf n))).mpr
  intro ns hns
  obtain ⟨ms,hms,hf'⟩:=(hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hf'] with ω hω
  exact hφ.continuousAt.tendsto.comp hω

/-- Every finite vector of actual probability limits converges jointly. -/
theorem fin : ∀m:ℕ,∀(f:ℕ→Ω→Fin m→E)(X:Ω→Fin m→E),
    (∀n i,Measurable (fun ω=>f n ω i))→
    (∀i,TendstoInMeasure μ (fun n ω=>f n ω i) atTop (fun ω=>X ω i))→
    TendstoInMeasure μ f atTop X:=by
  intro m
  induction m with
  | zero =>
    intro f X hf hX
    apply tendstoInMeasure_of_tendsto_ae
      (fun n=>aestronglyMeasurable_zero.congr (ae_of_all _ (fun ω=>Subsingleton.elim _ _)))
    exact ae_of_all _ (fun ω=>by
      have he:(fun n=>f n ω)=(fun _:ℕ=>X ω):=funext (fun _=>Subsingleton.elim _ _)
      rw [he]
      exact tendsto_const_nhds)
  | succ m ih =>
    intro f X hf hX
    let tail:ℕ→Ω→Fin m→E:=fun n ω i=>f n ω i.succ
    have ht:=ih tail (fun ω i=>X ω i.succ) (fun n i=>hf n i.succ) (fun i=>hX i.succ)
    have hp:=prod μ (fun n ω=>f n ω 0) tail (fun ω=>X ω 0) (fun ω i=>X ω i.succ)
      (fun n=>(hf n 0).aestronglyMeasurable)
      (fun n=>(measurable_pi_iff.mpr (fun (i:Fin m)=>hf n i.succ)).aestronglyMeasurable) (hX 0) ht
    have hc:Continuous (fun z:E×(Fin m→E)=>(Fin.cons z.1 z.2:Fin (m+1)→E)):=by fun_prop
    have hh:=continuous_map μ _ _
      (fun n=>(hf n 0).aestronglyMeasurable.prodMk
        (measurable_pi_iff.mpr (fun (i:Fin m)=>hf n i.succ)).aestronglyMeasurable) hp _ hc
    have he1:(fun n ω=>(Fin.cons (f n ω 0) (fun i=>f n ω i.succ):Fin (m+1)→E))=f:=by
      funext n ω i
      exact Fin.cases rfl (fun j=>rfl) i
    have he2:(fun ω=>(Fin.cons (X ω 0) (fun i=>X ω i.succ):Fin (m+1)→E))=X:=by
      funext ω i
      exact Fin.cases rfl (fun j=>rfl) i
    change TendstoInMeasure μ (fun n ω=>(Fin.cons (f n ω 0) (fun i=>f n ω i.succ):Fin (m+1)→E)) atTop
      (fun ω=>(Fin.cons (X ω 0) (fun i=>X ω i.succ):Fin (m+1)→E)) at hh
    rw [he1,he2] at hh
    exact hh
end SHE.FiniteJointProbabilityLimit
