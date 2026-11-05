module

public import SHEStochastic.EnergyClipping
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.FixedLawEnergy
open MeasureTheory Filter
open scoped ENNReal Topology

/-- A common law makes the energy tails exactly equal, even on
different spaces and with arbitrary dependence on other state variables. -/
theorem uniform_tails {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    {E : Type*} [MeasurableSpace E] (P : ∀ m,Measure (Ω m))
    (X : ∀ m,Ω m → E) (hX : ∀ m,Measurable (X m))
    (ν : Measure E) (hlaw : ∀ m,(P m).map (X m)=ν)
    (energy : E → ℝ) (he : Measurable energy) (hi : Integrable energy ν) :
    Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤energy (X m x)},
      ENNReal.ofReal (energy (X m x)) ∂P m) atTop (𝓝 0) := by
  have htail (R : ℕ) (m : ℕ) :
      (∫⁻ x in {x | (R : ℝ)≤energy (X m x)},ENNReal.ofReal (energy (X m x)) ∂P m)=
        ∫⁻ z in {z | (R : ℝ)≤energy z},ENNReal.ofReal (energy z) ∂ν := by
    rw [←hlaw m,setLIntegral_map (measurableSet_le measurable_const he) he.ennreal_ofReal (hX m)]
    rfl
  have ht := EnergyClipping.tails_tendsto ν energy he hi
  simpa only [htail, iSup_const] using ht

/-- The same criterion with integrability checked directly on the
zeroth actual source space, rather than separately on its pushforward. -/
theorem of_common_map {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    {E : Type*} [MeasurableSpace E] (P : ∀ m,Measure (Ω m))
    (X : ∀ m,Ω m → E) (hX : ∀ m,Measurable (X m))
    (hlaw : ∀ m,(P m).map (X m)=(P 0).map (X 0))
    (energy : E → ℝ) (he : Measurable energy)
    (hi : Integrable (fun x => energy (X 0 x)) (P 0)) :
    Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤energy (X m x)},
      ENNReal.ofReal (energy (X m x)) ∂P m) atTop (𝓝 0) :=
  uniform_tails P X hX _ hlaw energy he
    ((integrable_map_measure he.aestronglyMeasurable (hX 0).aemeasurable).mpr hi)

end SHEStochastic.FixedLawEnergy
