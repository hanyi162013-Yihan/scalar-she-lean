module

public import SHE.StandardTerminalPastLocality
public import SHE.PastItoAlgebra
public import SHE.PredictablePastParameter

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.PastSimpleItoSelection
open Set MeasureTheory PredictableL2 PastItoInputs
open scoped NNReal ENNReal
open Classical
variable {Ω X C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
variable (v : ℝ≥0) (U : X → Process (E := C) 𝓕 μ H)
variable (s : @SimpleFunc Ω (𝓕 v) X)
local notation "sr" => @SimpleFunc.range Ω X (𝓕 v) s
local notation "sf" => @SimpleFunc.measurableSet_fiber Ω X (𝓕 v) s
local notation "sm" => @SimpleFunc.mem_range_self Ω X (𝓕 v) s

/-- Finite past-simple selection uses the original predictable input
space, and is supported strictly after the same deterministic past. -/
def input : Process (E := C) 𝓕 μ H :=
  ∑ x ∈ sr, eventProcess 𝓕 μ H v {ω | s ω=x} (sf x) (U x)

theorem input_ae :
    input 𝓕 μ H v U s =ᵐ[energyMeasure μ H]
      fun p => if v<p.1 then U (s p.2) p else 0 := by
  have he := (Filter.eventually_all_finset sr).mpr (fun x _ =>
    eventProcess_ae 𝓕 μ H v {ω | s ω=x} (sf x) (U x))
  have hs := ae_eq_of_ae_eq_trim (Lp.coeFn_finsetSum sr (fun x =>
    eventProcess 𝓕 μ H v {ω | s ω=x} (sf x) (U x)))
  filter_upwards [he,hs] with p hp hsum
  change input 𝓕 μ H v U s p=_
  rw [input,hsum]
  simp only [Finset.sum_apply]
  have hsumEq : (∑ x∈sr,eventProcess 𝓕 μ H v {ω | s ω=x} (sf x) (U x) p)=
      ∑ x∈sr,(eventAfter v {ω | s ω=x}).indicator (U x) p :=
    Finset.sum_congr rfl (fun x hx => hp x hx)
  rw [hsumEq]
  by_cases ht : v<p.1
  · rw [ite_eq_left ht]
    calc
      _ = (eventAfter v {ω | s ω=s p.2}).indicator (U (s p.2)) p := by
        apply Finset.sum_eq_single (s p.2)
        · intro x hx hne
          simp [eventAfter,ht,Ne.symm hne]
        · exact fun hn => (hn (sm p.2)).elim
      _ = _ := by simp [eventAfter,ht]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro x hx
    simp [eventAfter,ht]

variable [SFinite μ]
variable (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ H)

/-- Ordinary past-event pullout identifies a finite selected original
integral exactly. No independent restarted integral is introduced. -/
theorem integral_ae (hlocal : StandardTerminalPastLocality I) :
    I.integral (input 𝓕 μ H v U s) =ᵐ[μ]
      fun ω => I.integral (post 𝓕 μ H v (U (s ω))) ω := by
  have he := (Filter.eventually_all_finset sr).mpr (fun x _ =>
    hlocal v {ω | s ω=x} (sf x) (U x))
  have hs := Lp.coeFn_finsetSum sr (fun x =>
    I.integral (eventProcess 𝓕 μ H v {ω | s ω=x} (sf x) (U x)))
  filter_upwards [he,hs] with ω hω hsum
  change I.integral (∑ x∈sr,eventProcess 𝓕 μ H v {ω | s ω=x} (sf x) (U x)) ω=_
  rw [map_sum,hsum]
  simp only [Finset.sum_apply]
  calc
    _ = I.integral (eventProcess 𝓕 μ H v {omega1 | s omega1=s ω} (sf (s ω)) (U (s ω))) ω := by
      apply Finset.sum_eq_single (s ω)
      · intro x hx hne
        rw [hω x hx]
        simp [Ne.symm hne]
      · exact fun hn => (hn (sm ω)).elim
    _ = _ := by rw [hω (s ω) (sm ω)]; simp

end SHE.PastSimpleItoSelection
