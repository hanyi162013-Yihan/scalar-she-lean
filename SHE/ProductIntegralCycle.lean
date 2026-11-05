module

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.ProductIntegralCycle
open MeasureTheory
variable {A T C Ω : Type*} [MeasurableSpace A] [MeasurableSpace T] [MeasurableSpace C] [MeasurableSpace Ω]

def cycle : (A × (T × C)) × Ω ≃ᵐ ((A × Ω) × T) × C :=
  (MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl A).prodCongr (MeasurableEquiv.prodComm : (T × C) × Ω ≃ᵐ Ω × (T × C)))).trans
    (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodAssoc.symm)

theorem measurePreserving_cycle (μ : Measure A) (ν : Measure T) (σ : Measure C) (τ : Measure Ω)
    [SFinite μ] [SFinite ν] [SFinite σ] [SFinite τ] :
    MeasurePreserving (cycle (A := A) (T := T) (C := C) (Ω := Ω))
      ((μ.prod (ν.prod σ)).prod τ) (((μ.prod τ).prod ν).prod σ) := by
  have h₁ := measurePreserving_prodAssoc μ (ν.prod σ) τ
  have h₂ := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν.prod σ) (ν := τ))
  have h₃ := MeasurePreserving.symm (MeasurableEquiv.prodAssoc : (A × Ω) × (T × C) ≃ᵐ A × (Ω × (T × C)))
    (measurePreserving_prodAssoc μ τ (ν.prod σ))
  have h₄ := MeasurePreserving.symm (MeasurableEquiv.prodAssoc : ((A × Ω) × T) × C ≃ᵐ (A × Ω) × (T × C))
    (measurePreserving_prodAssoc (μ.prod τ) ν σ)
  exact h₄.comp (h₃.comp (h₂.comp h₁))

theorem integral_cycle (μ : Measure A) (ν : Measure T) (σ : Measure C) (τ : Measure Ω)
    [SFinite μ] [SFinite ν] [SFinite σ] [SFinite τ] (f : A → T × C → Ω → ℝ) :
    (∫ p : (A × (T × C)) × Ω,f p.1.1 p.1.2 p.2 ∂(μ.prod (ν.prod σ)).prod τ)=
      ∫ q : ((A × Ω) × T) × C,f q.1.1.1 (q.1.2,q.2) q.1.1.2 ∂((μ.prod τ).prod ν).prod σ :=
  (measurePreserving_cycle μ ν σ τ).integral_comp'
    (fun q => f q.1.1.1 (q.1.2,q.2) q.1.1.2)

theorem integral_cycle_iterated (μ : Measure A) (ν : Measure T) (σ : Measure C) (τ : Measure Ω)
    [SFinite μ] [SFinite ν] [SFinite σ] [SFinite τ] (f : A → T × C → Ω → ℝ)
    (hf : Integrable (fun q : ((A × Ω) × T) × C => f q.1.1.1 (q.1.2,q.2) q.1.1.2)
      (((μ.prod τ).prod ν).prod σ)) :
    (∫ p : (A × (T × C)) × Ω,f p.1.1 p.1.2 p.2 ∂(μ.prod (ν.prod σ)).prod τ)=
      ∫ q : (A × Ω) × T,∫ x : C,f q.1.1 (q.2,x) q.1.2 ∂σ ∂(μ.prod τ).prod ν := by
  rw [integral_cycle μ ν σ τ f]
  exact integral_prod _ hf

end SHE.ProductIntegralCycle
