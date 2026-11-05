module

public import SHEStochastic.ContinuousNormExit
public import SHEStochastic.StoppedPathPasting
public import SHE.NativeContinuousPath
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.ContinuousPathExitNorm
open SHE MeasureTheory Set StoppedPathPasting
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual compact-interval path norm reaches a level exactly
when the original continuous process exits that closed norm level. -/
theorem le_iff (H : ℝ≥0) (U : ℝ≥0 → Ω → E) (hc : ∀ ω,Continuous (fun t => U t ω))
    (N : ℕ) (ω : Ω) :
    (N : ℝ)≤‖NativeContinuousPath.path H U hc ω‖ ↔
      ContinuousNormExit.exit U N ω≤(H : WithTop ℝ≥0) := by
  let p := NativeContinuousPath.path H U hc ω
  constructor
  · intro hN
    obtain ⟨t,_,hmax⟩ := isCompact_univ.exists_isMaxOn
      (show (Set.univ : Set (Time H)).Nonempty from ⟨origin H,Set.mem_univ _⟩) p.continuous.norm.continuousOn
    have hn : ‖p‖≤‖p t‖ := (ContinuousMap.norm_le p (norm_nonneg _)).mpr
      (fun s => hmax (Set.mem_univ s))
    apply (ContinuousNormExit.le_iff U hc N H ω).mpr
    exact ⟨t.val.toNNReal,⟨bot_le,by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal t.property.2⟩,hN.trans hn⟩
  · intro he
    obtain ⟨s,hs,hN⟩ := (ContinuousNormExit.le_iff U hc N H ω).mp he
    let t : Time H := ⟨s,⟨s.coe_nonneg,by exact_mod_cast hs.2⟩⟩
    have hp : p t=U s ω := by
      change U (s : ℝ).toNNReal ω=U s ω
      rw [Real.toNNReal_coe]
    exact hN.trans (hp ▸ p.norm_coe_le_norm t)

end SHEStochastic.ContinuousPathExitNorm
