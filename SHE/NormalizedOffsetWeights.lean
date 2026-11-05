module

public import SHE.NormalizedLeafOffsets
public import SHE.PastEventWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NormalizedLeafOffsets
open Set MeasureTheory Real
variable {Ω : Type*} {m0 past : MeasurableSpace Ω} {m : ℕ}

/-- Actual conditional event moments control the original normalized
leaf-offset budget against ANY integrable past-measurable weight. -/
theorem weighted_budget (μ : @Measure Ω m0) [IsFiniteMeasure μ]
    (hpast : past≤m0) (age : Fin m→ℝ) (hage : ∀j,0<age j)
    (offset : Ω→Fin m→ℝ) (hoffset : Measurable[m0] offset) (power degree C : ℝ)
    (hC : 0≤C)
    (hmoment : ∀A,MeasurableSet[past] A→∀j,
      Integrable (fun ω=>|offset ω j|^power) (μ.restrict A) ∧
        (∫ω in A,|offset ω j|^power ∂μ)≤C*(age j)^degree*μ.real A)
    (weight : Ω→ℝ) (hw : Measurable[past] weight) (hw0 : ∀ω,0≤weight ω) (hwi : Integrable weight μ) :
    let B:=fun ω=>budget age (offset ω) power degree
    Integrable (fun ω=>weight ω*B ω) μ ∧
      (∫ω,weight ω*B ω ∂μ)≤((m:ℝ)*C)*(∫ω,weight ω ∂μ) := by
  letI : MeasurableSpace Ω:=m0
  intro B
  have hm : Measurable B:=budget_measurable age offset hoffset power degree
  have hB (ω : Ω) : 0≤B ω:=budget_nonneg age (offset ω) power degree hage
  have hBi (A : Set Ω) (hA : MeasurableSet[past] A) : Integrable B (μ.restrict A):=
    budget_integrable (μ.restrict A) age offset power degree (fun j=>(hmoment A hA j).1)
  have hb (A : Set Ω) (hA : MeasurableSet[past] A) :
      (∫ω in A,B ω ∂μ)≤((m:ℝ)*C)*μ.real A := by
    have hh:=integral_budget_le (μ.restrict A) age hage offset power degree C
      (fun j=>(hmoment A hA j).1)
      (fun j=>by simpa only [measureReal_restrict_apply_univ] using (hmoment A hA j).2)
    simpa only [measureReal_restrict_apply_univ] using hh
  have hi : Integrable B μ:=by
    simpa only [Measure.restrict_univ] using hBi univ MeasurableSet.univ
  exact PastEventWeights.weighted_integral μ hpast B hm hi hB ((m:ℝ)*C)
    (mul_nonneg (Nat.cast_nonneg _) hC) hb weight hw hw0 hwi

end SHE.NormalizedLeafOffsets
