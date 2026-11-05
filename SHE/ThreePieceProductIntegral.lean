module

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.ThreePieceProductIntegral
open MeasureTheory

/-- Absolute section budgets for three literal summands give genuine
product integrability of their jointly measurable sum. No cancellation
of an inner integral is used to establish Fubini. -/
theorem integrable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
    (τ : Measure Θ) (ν : Measure Y) [SFinite τ] [SFinite ν]
    (F C M B : Θ×Y→ℝ) (hF : Measurable F)
    (heq : ∀ z,F z=C z+M z+B z)
    (Ec Em Eb : Θ→ℝ) (hEc : Integrable Ec τ) (hEm : Integrable Em τ) (hEb : Integrable Eb τ)
    (hC : ∀ᵐ θ ∂τ,Integrable (fun y=>C (θ,y)) ν ∧ (∫ y,|C (θ,y)| ∂ν)≤Ec θ)
    (hM : ∀ᵐ θ ∂τ,Integrable (fun y=>M (θ,y)) ν ∧ (∫ y,|M (θ,y)| ∂ν)≤Em θ)
    (hB : ∀ᵐ θ ∂τ,Integrable (fun y=>B (θ,y)) ν ∧ (∫ y,|B (θ,y)| ∂ν)≤Eb θ) :
    Integrable F (τ.prod ν) ∧
      (∫ z,|F z| ∂τ.prod ν)≤∫ θ,Ec θ+Em θ+Eb θ ∂τ := by
  have hs : ∀ᵐ θ ∂τ,Integrable (fun y=>F (θ,y)) ν ∧
      (∫ y,‖F (θ,y)‖ ∂ν)≤Ec θ+Em θ+Eb θ := by
    filter_upwards [hC,hM,hB] with θ hθC hθM hθB
    have hi : Integrable (fun y=>F (θ,y)) ν:=
      ((hθC.1.add hθM.1).add hθB.1).congr (ae_of_all _ (fun y=>(heq (θ,y)).symm))
    refine ⟨hi,?_⟩
    calc
      _≤∫ y,|C (θ,y)|+|M (θ,y)|+|B (θ,y)| ∂ν := by
        apply integral_mono hi.norm ((hθC.1.abs.add hθM.1.abs).add hθB.1.abs)
        intro y
        change ‖F (θ,y)‖≤|C (θ,y)|+|M (θ,y)|+|B (θ,y)|
        rw [Real.norm_eq_abs,heq]
        have hn : ‖C (θ,y)+M (θ,y)+B (θ,y)‖≤‖C (θ,y)‖+‖M (θ,y)‖+‖B (θ,y)‖:=
          (norm_add_le (C (θ,y)+M (θ,y)) (B (θ,y))).trans
            (add_le_add (norm_add_le (C (θ,y)) (M (θ,y))) (le_refl ‖B (θ,y)‖))
        simpa only [Real.norm_eq_abs] using hn
      _=(∫ y,|C (θ,y)| ∂ν)+(∫ y,|M (θ,y)| ∂ν)+(∫ y,|B (θ,y)| ∂ν) := by
        have h1:=integral_add (hθC.1.abs.add hθM.1.abs) hθB.1.abs
        have h2:=integral_add hθC.1.abs hθM.1.abs
        simpa only [Pi.add_apply] using h1.trans (congrArg (fun x:ℝ=>x+∫ y,|B (θ,y)| ∂ν) h2)
      _≤Ec θ+Em θ+Eb θ:=add_le_add (add_le_add hθC.2 hθM.2) hθB.2
  have hNm : Measurable (fun θ=>∫ y,‖F (θ,y)‖ ∂ν):=
    hF.norm.stronglyMeasurable.integral_prod_right'.measurable
  have hNi : Integrable (fun θ=>∫ y,‖F (θ,y)‖ ∂ν) τ:=
    ((hEc.add hEm).add hEb).mono' hNm.aestronglyMeasurable (hs.mono (fun θ hθ=>by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
      exact hθ.2))
  have hFi : Integrable F (τ.prod ν):=
    (integrable_prod_iff hF.aestronglyMeasurable).mpr ⟨hs.mono (fun _ h=>h.1),hNi⟩
  refine ⟨hFi,?_⟩
  have hp:=integral_prod (f:=fun z=>‖F z‖) hFi.norm
  simp only [Real.norm_eq_abs] at hp hNi
  rw [hp]
  apply integral_mono_ae hNi ((hEc.add hEm).add hEb)
  filter_upwards [hs] with θ hθ
  change (∫ y,|F (θ,y)| ∂ν)≤Ec θ+Em θ+Eb θ
  simpa only [Real.norm_eq_abs] using hθ.2

end SHE.ThreePieceProductIntegral
