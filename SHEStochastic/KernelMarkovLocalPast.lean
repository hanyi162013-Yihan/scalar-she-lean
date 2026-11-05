module

public import SHEStochastic.KernelMarkovFreshLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.KernelMarkovLocalPast
open MeasureTheory ProbabilityTheory KernelMarkovTrajectory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Kernel independence from the new block's local past lifts to
independence from that local past AND all preceding blocks. Thus
continuation retains the full filtration, not just endpoint laws. -/
theorem prefix_local_product (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] (n : ℕ)
    (g : X → Z) (hg : Measurable g) (f : X → Y) (hf : Measurable f)
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (h : ∀ᵐ x ∂(law μ₀ K).map (fun p => p n),
      (K n x).map (fun y => (g y,f y))=((K n x).map g).prod ν) :
    (law μ₀ K).map (fun p => ((Preorder.frestrictLe n p,g (p (n+1))),f (p (n+1))))=
      ((law μ₀ K).map (fun p => (Preorder.frestrictLe n p,g (p (n+1))))).prod ν := by
  let Q := law μ₀ K
  let P := Q.map (Preorder.frestrictLe n)
  let L := (transition K n).map g
  let T : Kernel (((i : Finset.Iic n) → X)×Z) Y := Kernel.const _ ν
  have hLast : P.map (last n)=Q.map (fun p => p n) := by
    rw [Measure.map_map (last_measurable n) (by fun_prop)]
    rfl
  have hPre : ∀ᵐ x ∂P,(K n (last n x)).map (fun y => (g y,f y))=
      ((K n (last n x)).map g).prod ν := by
    apply ae_of_ae_map (μ := P)
      (p := fun x => (K n x).map (fun y => (g y,f y))=((K n x).map g).prod ν)
      (last_measurable n).aemeasurable
    rw [hLast]
    exact h
  have hComp (x : (i : Finset.Iic n) → X) : (L ⊗ₖ T) x=(L x).prod ν := by
    ext s hs
    rw [Kernel.compProd_apply hs,Measure.prod_apply hs]
    rfl
  have hK : (transition K n).map (fun y => (g y,f y)) =ᵐ[P] L ⊗ₖ T := by
    filter_upwards [hPre] with x hx
    rw [Kernel.map_apply _ (hg.prodMk hf),hComp]
    simpa only [L,Kernel.map_apply _ hg,transition,Kernel.comap_apply] using hx
  have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => X) (μ₀ := μ₀) (κ := transition K) (a := n)
  change P ⊗ₘ transition K n=Q.map (fun p => (Preorder.frestrictLe n p,p (n+1))) at he
  have hPast : Q.map (fun p => (Preorder.frestrictLe n p,g (p (n+1))))=P ⊗ₘ L := by
    dsimp only [L]
    rw [Measure.compProd_map hg,he,Measure.map_map (measurable_id.prodMap hg) (by fun_prop)]
    rfl
  calc
    _ = ((P ⊗ₘ transition K n).map (Prod.map id (fun y => (g y,f y)))).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [he,Measure.map_map (measurable_id.prodMap (hg.prodMk hf)) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (P ⊗ₘ (transition K n).map (fun y => (g y,f y))).map MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.compProd_map (hg.prodMk hf)]
    _ = (P ⊗ₘ (L ⊗ₖ T)).map MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.compProd_congr hK]
    _ = (P ⊗ₘ L) ⊗ₘ T := Measure.compProd_assoc
    _ = (P ⊗ₘ L).prod ν := Measure.compProd_const
    _ = _ := by rw [←hPast]

end SHEStochastic.KernelMarkovLocalPast
