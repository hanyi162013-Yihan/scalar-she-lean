module

public import SHEStochastic.KernelMarkovFreshLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.KernelFixedStatisticLaw
open MeasureTheory ProbabilityTheory
variable {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]

/-- Replacing the retained past by any measurable statistic preserves
its independence from a future variable with fixed law. -/
theorem map_first {W : Type*} [MeasurableSpace W]
    (Q : Measure X) (g : X → Z) (f : X → Y) (hg : Measurable g) (hf : Measurable f)
    (ν : Measure Y) [SFinite ν]
    (h : Q.map (fun x => (g x,f x))=(Q.map g).prod ν)
    (a : Z → W) (ha : Measurable a) :
    Q.map (fun x => (a (g x),f x))=(Q.map (a ∘ g)).prod ν := by
  have hh := congrArg (fun η => η.map (Prod.map a id)) h
  rw [Measure.map_map (ha.prodMap measurable_id) (hg.prodMk hf),
    ←Measure.map_prod_map (Q.map g) ν ha measurable_id,Measure.map_id,
    Measure.map_map ha hg] at hh
  exact hh

theorem independent_of_product (Q : Measure X) [IsProbabilityMeasure Q]
    (g : X → Z) (f : X → Y) (hg : Measurable g) (hf : Measurable f)
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (h : Q.map (fun x => (g x,f x))=(Q.map g).prod ν) :
    IndepFun g f Q ∧ HasLaw f ν Q := by
  have hLaw : Q.map f=ν := by
    have hh := congrArg (fun η => η.map Prod.snd) h
    rw [Measure.map_map measurable_snd (hg.prodMk hf),Measure.map_snd_prod] at hh
    simpa only [Function.comp_def,Measure.map_apply hg MeasurableSet.univ,
      Set.preimage_univ,measure_univ,one_smul] using hh
  refine ⟨?_,⟨hf.aemeasurable,hLaw⟩⟩
  exact (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hf.aemeasurable).mpr
    (h.trans (congrArg (fun η => (Q.map g).prod η) hLaw.symm))

/-- Mixing conditional laws with one fixed statistic law preserves
that law. This applies to the first block as well as continuation blocks. -/
theorem law (ρ : Measure Z) [IsProbabilityMeasure ρ] (κ : Kernel Z X) [IsMarkovKernel κ]
    (Q : Measure X) (hQ : (ρ ⊗ₘ κ).map Prod.snd=Q)
    (f : X → Y) (hf : Measurable f) (ν : Measure Y) [IsProbabilityMeasure ν]
    (h : ∀ᵐ z ∂ρ,(κ z).map f=ν) : Q.map f=ν := by
  have hk : κ.map f =ᵐ[ρ] Kernel.const Z ν := by
    filter_upwards [h] with z hz
    simpa only [Kernel.map_apply _ hf,Kernel.const_apply] using hz
  rw [←hQ,Measure.map_map hf measurable_snd]
  calc
    _ = ((ρ ⊗ₘ κ).map (Prod.map id f)).map Prod.snd := by
      rw [Measure.map_map measurable_snd (measurable_id.prodMap hf)]
      rfl
    _ = (ρ ⊗ₘ κ.map f).map Prod.snd := by rw [Measure.compProd_map hf]
    _ = (ρ ⊗ₘ Kernel.const Z ν).map Prod.snd := by rw [Measure.compProd_congr hk]
    _ = ν := by rw [Measure.compProd_const,Measure.map_snd_prod,measure_univ,one_smul]

/-- Conditional independence with a fixed future law survives mixing
over the initial state, even though the past statistic's law varies. -/
theorem local_product {W : Type*} [MeasurableSpace W]
    (ρ : Measure Z) [IsProbabilityMeasure ρ] (κ : Kernel Z X) [IsMarkovKernel κ]
    (Q : Measure X) (hQ : (ρ ⊗ₘ κ).map Prod.snd=Q)
    (g : X → W) (hg : Measurable g) (f : X → Y) (hf : Measurable f)
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (h : ∀ᵐ z ∂ρ,(κ z).map (fun x => (g x,f x))=((κ z).map g).prod ν) :
    Q.map (fun x => (g x,f x))=(Q.map g).prod ν := by
  let L := κ.map g
  let T : Kernel (Z×W) Y := Kernel.const _ ν
  have hComp (z : Z) : (L ⊗ₖ T) z=(L z).prod ν := by
    ext s hs
    rw [Kernel.compProd_apply hs,Measure.prod_apply hs]
    rfl
  have hk : κ.map (fun x => (g x,f x)) =ᵐ[ρ] L ⊗ₖ T := by
    filter_upwards [h] with z hz
    rw [Kernel.map_apply _ (hg.prodMk hf),hComp]
    simpa only [L,Kernel.map_apply _ hg] using hz
  have hJoint : (ρ ⊗ₘ κ).map (fun q => ((q.1,g q.2),f q.2))=(ρ ⊗ₘ L).prod ν := by
    calc
      _ = ((ρ ⊗ₘ κ).map (Prod.map id (fun x => (g x,f x)))).map
          MeasurableEquiv.prodAssoc.symm := by
        rw [Measure.map_map (by fun_prop) (measurable_id.prodMap (hg.prodMk hf))]
        rfl
      _ = (ρ ⊗ₘ κ.map (fun x => (g x,f x))).map MeasurableEquiv.prodAssoc.symm := by
        rw [Measure.compProd_map (hg.prodMk hf)]
      _ = (ρ ⊗ₘ (L ⊗ₖ T)).map MeasurableEquiv.prodAssoc.symm := by rw [Measure.compProd_congr hk]
      _ = (ρ ⊗ₘ L) ⊗ₘ T := Measure.compProd_assoc
      _ = _ := Measure.compProd_const
  have hDrop := congrArg (fun η => η.map (Prod.map Prod.snd id)) hJoint
  rw [Measure.map_map (measurable_snd.prodMap measurable_id) (by fun_prop),
    ←Measure.map_prod_map (ρ ⊗ₘ L) ν measurable_snd measurable_id,Measure.map_id] at hDrop
  have hPast : (ρ ⊗ₘ L).map Prod.snd=Q.map g := by
    dsimp only [L]
    rw [Measure.compProd_map hg,Measure.map_map measurable_snd (measurable_id.prodMap hg),
      ←hQ,Measure.map_map hg measurable_snd]
    rfl
  rw [hPast] at hDrop
  conv_lhs => rw [←hQ,Measure.map_map (hg.prodMk hf) measurable_snd]
  exact hDrop

end SHEStochastic.KernelFixedStatisticLaw
