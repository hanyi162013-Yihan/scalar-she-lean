module

public import SHEStochastic.AEContinuousClosedSet
public import SHEStochastic.StoppedPathPasting
public import SHE.NativeContinuousPath
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.NativePathInteriorRecognition
open MeasureTheory Set SHE StoppedPathPasting
open scoped NNReal

def clipped (H t : ℝ≥0) : Time H :=
  ⟨min (t : ℝ) (H : ℝ),le_min t.property H.property,min_le_right _ _⟩

theorem continuous_clipped (H : ℝ≥0) : Continuous (clipped H) :=
  (NNReal.continuous_coe.min continuous_const).subtype_mk _

/-- Interior deterministic-time identities between continuous processes
identify their complete native paths, without separate endpoint estimates. -/
theorem path_eq {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (H : ℝ≥0) (hH : 0 < H) (U : ℝ≥0 → Ω → E)
    (hc : ∀ ω, Continuous (fun t => U t ω)) (V : Ω → Path H E)
    (he : ∀ s (hs0 : 0 < s) (hsH : s < H), U s =ᵐ[μ]
      fun ω => V ω ⟨(s : ℝ),hs0.le,hsH.le⟩) :
    NativeContinuousPath.path H U hc =ᵐ[μ] V := by
  have hh := AEContinuousClosedSet.ae_eq_closure μ U (fun s ω => V ω (clipped H s)) hc
    (fun ω => (V ω).continuous.comp (continuous_clipped H)) (Ioo 0 H)
    (fun s hs => (he s hs.1 hs.2).mono fun ω h => by
      convert h using 1
      apply congrArg (V ω)
      apply Subtype.ext
      exact min_eq_left (show (s : ℝ) ≤ (H : ℝ) from hs.2.le))
  rw [closure_Ioo (ne_of_lt hH)] at hh
  filter_upwards [hh] with ω hω
  apply ContinuousMap.ext
  intro t
  have ht : t.val.toNNReal ≤ H := Real.toNNReal_le_iff_le_coe.mpr t.property.2
  have h := hω t.val.toNNReal ⟨zero_le,ht⟩
  have heval : clipped H t.val.toNNReal = t := by
    apply Subtype.ext
    simp only [clipped,Real.coe_toNNReal _ t.property.1,min_eq_left t.property.2]
  change U t.val.toNNReal ω = V ω t
  rwa [heval] at h

end SHEStochastic.NativePathInteriorRecognition
