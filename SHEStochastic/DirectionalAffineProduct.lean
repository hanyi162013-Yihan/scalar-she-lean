module

public import SHEStochastic.DirectionalJetBilinear

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

/-- Each position is retained separately, even when directions agree;
the remaining directions keep their original order. -/
def omissions : List E → List (E × List E)
  | [] => []
  | v::w => (v,w)::(omissions w).map (fun p => (p.1,v::p.2))

/-- Exact mixed differentiation of an affine field times a nonlinear
finite-dimensional coefficient. There is at most one differentiated
affine numerator in every term, as required by the vector column
estimates. This holds in actual Banach-valued `L²` spaces as well. -/
theorem affine_bilinear (K : A →L[ℝ] B →L[ℝ] C) (a : A) (L : E →L[ℝ] A)
    (s : Set E) (hs : IsOpen s) (x : E) (hx : x∈s) (w : List E)
    (g : E → B) (hg : ∀ y∈s, ContDiffAt ℝ ∞ g y) :
    jet w (fun y => K (a+L y) (g y)) x=
      K (a+L x) (jet w g x)+
        ((omissions w).map (fun p => K (L p.1) (jet p.2 g x))).sum := by
  have ha (y : E) : ContDiffAt ℝ ∞ (fun z => a+L z) y :=
    contDiffAt_const.add L.contDiff.contDiffAt
  induction w generalizing g with
  | nil => simp only [jet, omissions, List.map_nil, List.sum_nil, add_zero]
  | cons v w ih =>
    have he : directional v (fun y => K (a+L y) (g y)) =ᶠ[𝓝 x]
        (fun y => K (L v) (g y)+K (a+L y) (directional v g y)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      change fderiv ℝ (fun z => K (a+L z) (g z)) y v=_
      rw [K.fderiv_of_bilinear
        ((ha y).differentiableAt (by simp))
        ((hg y hy).differentiableAt (by simp))]
      change K (a+L y) (directional v g y)+
        K (fderiv ℝ (fun z => a+L z) y v) (g y)=_
      rw [fderiv_const_add, L.fderiv]
      exact add_comm _ _
    change jet w (directional v (fun y => K (a+L y) (g y))) x=_
    calc
      _ = jet w (fun y => K (L v) (g y)+K (a+L y) (directional v g y)) x := congr w he
      _ = jet w (fun y => K (L v) (g y)) x+
          jet w (fun y => K (a+L y) (directional v g y)) x :=
        add s hs x hx w _ _
          (fun y hy => (K (L v)).contDiff.contDiffAt.comp y (hg y hy))
          (fun y hy => bilinear_smooth K (ha y)
            (directional_smooth (hg y hy) v))
      _ = K (L v) (jet w g x)+
          (K (a+L x) (jet w (directional v g) x)+
            ((omissions w).map (fun p => K (L p.1) (jet p.2 (directional v g) x))).sum) := by
        rw [clm (K (L v)) s hs x hx w g hg, ih _ (fun y hy => directional_smooth (hg y hy) v)]
      _ = _ := by
        simp only [omissions, List.map_cons, List.map_map, Function.comp_def, List.sum_cons, jet]
        abel

end SHEStochastic.DirectionalJets
