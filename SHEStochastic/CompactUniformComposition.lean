module

public import Mathlib.Topology.UniformSpace.CompactConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.CompactUniformComposition
open Filter
open scoped Topology
variable {ι A B C : Type*} [TopologicalSpace A] [UniformSpace B] [UniformSpace C]

/-- Uniform convergence is retained by every cofinal reindexing. -/
theorem reindex {κ : Type*} {F : ι → A → B} {f : A → B} {p : Filter ι} {q : Filter κ}
    {s : Set A} {φ : κ → ι} (h : TendstoUniformlyOn F f p s) (hφ : Tendsto φ q p) :
    TendstoUniformlyOn (fun k x => F (φ k) x) f q s := by
  intro V hV
  exact hφ (h V hV)

/-- On a compact domain, uniform limits of continuous maps may be
postcomposed by an arbitrary continuous map. Compact-open continuity
supplies the argument, without a global Lipschitz bound on that map. -/
theorem postcompose {F : ι → A → B} {f : A → B} {p : Filter ι} {s : Set A}
    (hs : IsCompact s) (hF : ∀ i,Continuous (F i)) (hf : Continuous f)
    (hlim : TendstoUniformlyOn F f p s) (g : B → C) (hg : Continuous g) :
    TendstoUniformlyOn (fun i => g ∘ F i) (g ∘ f) p s := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let Fs : ι → C(s,B) := fun i => ⟨fun x => F i x.val,(hF i).comp continuous_subtype_val⟩
  let fs : C(s,B) := ⟨fun x => f x.val,hf.comp continuous_subtype_val⟩
  have ht : Tendsto Fs p (𝓝 fs) := ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hlim)
  have hh := (ContinuousMap.continuous_postcomp (X := s) ⟨g,hg⟩).tendsto fs |>.comp ht
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (ContinuousMap.tendsto_iff_tendstoUniformly.mp hh)

/-- The postcomposition may also depend continuously on the fixed
domain point. This covers full-history tests and fixed path observables. -/
theorem with_parameter {D : Type*} [UniformSpace D]
    {F : ι → D → B} {f : D → B} {p : Filter ι} {s : Set D}
    (hs : IsCompact s) (hF : ∀ i,Continuous (F i)) (hf : Continuous f)
    (hlim : TendstoUniformlyOn F f p s) (g : D×B → C) (hg : Continuous g) :
    TendstoUniformlyOn (fun i x => g (x,F i x)) (fun x => g (x,f x)) p s := by
  have hid : TendstoUniformlyOn (fun _ : ι => (id : D → D)) id p s := by
    intro V hV
    exact Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hV
  have hp : TendstoUniformlyOn (fun i x => (x,F i x)) (fun x => (x,f x)) p s := by
    intro V hV
    exact (tendsto_id.prodMk tendsto_id) ((hid.prodMk hlim) V hV)
  exact postcompose hs (fun i => continuous_id.prodMk (hF i))
    (continuous_id.prodMk hf) hp g hg

end SHEStochastic.CompactUniformComposition
