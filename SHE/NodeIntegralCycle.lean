module

public import SHE.ProductIntegralCycle

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.NodeIntegralCycle
open MeasureTheory
variable {A N Ω : Type*} [MeasurableSpace A] [MeasurableSpace N] [MeasurableSpace Ω]

def cycle : (A × N) × Ω ≃ᵐ (A × Ω) × N :=
  (MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl A).prodCongr (MeasurableEquiv.prodComm : N × Ω ≃ᵐ Ω × N))).trans
    MeasurableEquiv.prodAssoc.symm

theorem measurePreserving_cycle (μ : Measure A) (ν : Measure N) (τ : Measure Ω)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    MeasurePreserving (cycle (A := A) (N := N) (Ω := Ω))
      ((μ.prod ν).prod τ) ((μ.prod τ).prod ν) := by
  have h₁ := measurePreserving_prodAssoc μ ν τ
  have h₂ := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := τ))
  have h₃ := MeasurePreserving.symm (MeasurableEquiv.prodAssoc : (A × Ω) × N ≃ᵐ A × (Ω × N))
    (measurePreserving_prodAssoc μ τ ν)
  exact h₃.comp (h₂.comp h₁)

theorem integral_cycle (μ : Measure A) (ν : Measure N) (τ : Measure Ω)
    [SFinite μ] [SFinite ν] [SFinite τ] (f : A → N → Ω → ℝ) :
    (∫ q : (A × N) × Ω,f q.1.1 q.1.2 q.2 ∂(μ.prod ν).prod τ)=
      ∫ p : (A × Ω) × N,f p.1.1 p.2 p.1.2 ∂(μ.prod τ).prod ν :=
  (measurePreserving_cycle μ ν τ).integral_comp' (fun p => f p.1.1 p.2 p.1.2)

theorem integral_cycle_iterated (μ : Measure A) (ν : Measure N) (τ : Measure Ω)
    [SFinite μ] [SFinite ν] [SFinite τ] (f : A → N → Ω → ℝ)
    (hf : Integrable (fun p : (A × Ω) × N => f p.1.1 p.2 p.1.2) ((μ.prod τ).prod ν)) :
    (∫ q : (A × N) × Ω,f q.1.1 q.1.2 q.2 ∂(μ.prod ν).prod τ)=
      ∫ p : A × Ω,∫ z : N,f p.1 z p.2 ∂ν ∂μ.prod τ := by
  rw [integral_cycle μ ν τ f]
  exact integral_prod _ hf

end SHE.NodeIntegralCycle
