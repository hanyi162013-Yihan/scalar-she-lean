module

public import SHEStochastic.KernelMarkovTrajectory
public import Mathlib.Probability.HasLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.KernelMarkovFreshLaw
open MeasureTheory ProbabilityTheory KernelMarkovTrajectory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A statistic with the same law in every continuation kernel has
that law jointly with the ENTIRE existing prefix. This proves fresh
noise independence without discarding earlier solution coordinates. -/
theorem prefix_product (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] (n : ℕ)
    (f : X → Y) (hf : Measurable f) (ν : Measure Y) [IsProbabilityMeasure ν]
    (h : ∀ᵐ x ∂(law μ₀ K).map (fun p => p n),(K n x).map f=ν) :
    (law μ₀ K).map (fun p => (Preorder.frestrictLe n p,f (p (n+1))))=
      ((law μ₀ K).map (Preorder.frestrictLe n)).prod ν := by
  let Q := law μ₀ K
  let P := Q.map (Preorder.frestrictLe n)
  have hLast : P.map (last n)=Q.map (fun p => p n) := by
    rw [Measure.map_map (last_measurable n) (by fun_prop)]
    rfl
  have hPre : ∀ᵐ x ∂P,(K n (last n x)).map f=ν := by
    apply ae_of_ae_map (μ := P) (p := fun x => (K n x).map f=ν)
      (last_measurable n).aemeasurable
    rw [hLast]
    exact h
  have hK : (transition K n).map f =ᵐ[P] Kernel.const _ ν := by
    filter_upwards [hPre] with x hx
    simpa only [Kernel.map_apply _ hf,transition,Kernel.comap_apply,Kernel.const_apply] using hx
  have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => X) (μ₀ := μ₀) (κ := transition K) (a := n)
  change P ⊗ₘ transition K n=Q.map (fun p => (Preorder.frestrictLe n p,p (n+1))) at he
  calc
    _ = (P ⊗ₘ transition K n).map (Prod.map id f) := by
      rw [he,Measure.map_map (measurable_id.prodMap hf) (by fun_prop)]
      rfl
    _ = P ⊗ₘ (transition K n).map f := (Measure.compProd_map hf).symm
    _ = P ⊗ₘ Kernel.const _ ν := Measure.compProd_congr hK
    _ = P.prod ν := Measure.compProd_const

end SHEStochastic.KernelMarkovFreshLaw
