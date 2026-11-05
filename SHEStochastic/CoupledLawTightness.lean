module

public import SHEStochastic.TightnessFromCompactControl

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.CoupledLawTightness
open MeasureTheory Set
variable {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    {E V : Type*} [TopologicalSpace E] [TopologicalSpace V]
    [MeasurableSpace E] [MeasurableSpace V]

/-- Tight marginals give tight coupled laws across varying probability
spaces. The original initial-state/noise dependence is retained. -/
theorem paired (μ : ∀ m,Measure (Ω m)) (X : ∀ m,Ω m → E) (Y : ∀ m,Ω m → V)
    (hX : ∀ m,Measurable (X m)) (hY : ∀ m,Measurable (Y m))
    (htX : IsTightMeasureSet (Set.range (fun m => (μ m).map (X m))))
    (htY : IsTightMeasureSet (Set.range (fun m => (μ m).map (Y m)))) :
    IsTightMeasureSet (Set.range (fun m => (μ m).map (fun ω => (X m ω,Y m ω)))) := by
  let Q := fun m => (μ m).map (fun ω => (X m ω,Y m ω))
  have he₁ : Measure.fst '' Set.range Q=Set.range (fun m => (μ m).map (X m)) := by
    rw [←Set.range_comp']
    congr 1
    funext m
    exact Measure.fst_map_prodMk (hX m) (hY m)
  have he₂ : Measure.snd '' Set.range Q=Set.range (fun m => (μ m).map (Y m)) := by
    rw [←Set.range_comp']
    congr 1
    funext m
    exact Measure.snd_map_prodMk (hX m) (hY m)
  exact IsTightMeasureSet.prodMk (by rwa [he₁]) (by rwa [he₂])

/-- A prescribed initial law supplies its tight marginal automatically. -/
theorem with_initial (μ : ∀ m,Measure (Ω m)) (X : ∀ m,Ω m → E) (Y : ∀ m,Ω m → V)
    (hX : ∀ m,Measurable (X m)) (hY : ∀ m,Measurable (Y m))
    (ρ : Measure E) (hρtight : IsTightMeasureSet {ρ}) (hρ : ∀ m,(μ m).map (X m)=ρ)
    (htY : IsTightMeasureSet (Set.range (fun m => (μ m).map (Y m)))) :
    IsTightMeasureSet (Set.range (fun m => (μ m).map (fun ω => (X m ω,Y m ω)))) := by
  apply paired μ X Y hX hY _ htY
  simpa only [hρ,Set.range_const] using hρtight

end SHEStochastic.CoupledLawTightness
