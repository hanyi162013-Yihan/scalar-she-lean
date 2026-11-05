module

public import SHEStochastic.DirectionalJetBilinear

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.JetLinearConstraints
open Filter
open scoped Topology ContDiff
variable {E A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Every actual mixed derivative preserves a fixed bounded linear
constraint that holds on its smooth neighborhood. -/
theorem zero (L : A →L[ℝ] B) (s : Set E) (hs : IsOpen s) (x : E) (hx : x∈s)
    (f : E → A) (hf : ∀ y∈s, ContDiffAt ℝ ∞ f y) (hZero : ∀ y∈s, L (f y)=0)
    (w : List E) : L (DirectionalJets.jet w f x)=0 := by
  have he : (fun y => L (f y)) =ᶠ[𝓝 x] (fun _ => 0) :=
    (show ∀ᶠ y in 𝓝 x, y∈s from hs.mem_nhds hx).mono (fun y hy => hZero y hy)
  have hh := (DirectionalJets.congr w he).trans (DirectionalJets.jet_zero w x)
  rw [DirectionalJets.clm L s hs x hx w f hf] at hh
  exact hh

end SHEStochastic.JetLinearConstraints
