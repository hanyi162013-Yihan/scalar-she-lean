module

public import SHEStochastic.DirectionalJetFrechet
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.DirectionalJets
open Filter Set
open scoped Topology ContDiff

variable {E A B C : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

theorem bilinear_smooth (L : A →L[ℝ] B →L[ℝ] C) {f : E → A} {g : E → B} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => L (f y) (g y)) x :=
  (L.contDiff.contDiffAt.comp x hf).clm_apply hg

/-- The same ordered differentiation partitions apply to any bounded
bilinear operation, in particular matrix coefficients acting on actual
vector or matrix `L²` fields. -/
theorem bilinear (L : A →L[ℝ] B →L[ℝ] C) (s : Set E) (hs : IsOpen s)
    (x : E) (hx : x∈s) (w : List E) (f : E → A) (g : E → B)
    (hf : ∀ y∈s, ContDiffAt ℝ ∞ f y) (hg : ∀ y∈s, ContDiffAt ℝ ∞ g y) :
    jet w (fun y => L (f y) (g y)) x=
      ((pairs w).map (fun p => L (jet p.1 f x) (jet p.2 g x))).sum := by
  induction w generalizing f g with
  | nil => simp only [jet, pairs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | cons v w ih =>
    have he : directional v (fun y => L (f y) (g y)) =ᶠ[𝓝 x]
        (fun y => L (directional v f y) (g y)+L (f y) (directional v g y)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      change fderiv ℝ (fun z => L (f z) (g z)) y v=_
      rw [L.fderiv_of_bilinear ((hf y hy).differentiableAt (by simp))
        ((hg y hy).differentiableAt (by simp))]
      change L (f y) (directional v g y)+L (directional v f y) (g y)=_
      exact add_comm _ _
    change jet w (directional v (fun y => L (f y) (g y))) x=_
    calc
      _ = jet w (fun y => L (directional v f y) (g y)+L (f y) (directional v g y)) x := congr w he
      _ = jet w (fun y => L (directional v f y) (g y)) x+
          jet w (fun y => L (f y) (directional v g y)) x :=
        add s hs x hx w _ _
          (fun y hy => bilinear_smooth L (directional_smooth (hf y hy) v) (hg y hy))
          (fun y hy => bilinear_smooth L (hf y hy) (directional_smooth (hg y hy) v))
      _ = ((pairs w).map (fun p => L (jet p.1 (directional v f) x) (jet p.2 g x))).sum+
          ((pairs w).map (fun p => L (jet p.1 f x) (jet p.2 (directional v g) x))).sum :=
        congrArg₂ (·+·) (ih _ _ (fun y hy => directional_smooth (hf y hy) v) hg)
          (ih _ _ hf (fun y hy => directional_smooth (hg y hy) v))
      _ = _ := by simp only [pairs, List.map_append, List.sum_append, List.map_map, Function.comp_def, jet]

/-- Actual directional jets commute with a fixed bounded linear map,
including integration, cell restriction and coordinate projection. -/
theorem clm (L : A →L[ℝ] B) (s : Set E) (hs : IsOpen s) (x : E) (hx : x∈s)
    (w : List E) (f : E → A) (hf : ∀ y∈s, ContDiffAt ℝ ∞ f y) :
    jet w (fun y => L (f y)) x=L (jet w f x) := by
  induction w generalizing f with
  | nil => rfl
  | cons v w ih =>
    have he : directional v (fun y => L (f y)) =ᶠ[𝓝 x] fun y => L (directional v f y) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      have hh := L.hasFDerivAt.comp y ((hf y hy).differentiableAt (by simp)).hasFDerivAt
      exact congrArg (fun D : E →L[ℝ] B => D v) hh.fderiv
    exact (congr w he).trans (ih _ (fun y hy => directional_smooth (hf y hy) v))

end SHEStochastic.DirectionalJets
