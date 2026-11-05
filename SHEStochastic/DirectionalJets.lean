module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.DirectionalJets
open Filter Set
open scoped Topology ContDiff

section General

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def directional (v : E) (f : E → A) : E → A := fun x ↦ fderiv ℝ f x v

/-- Actual iterated directional derivatives; the first list entry acts
first. Matrix multiplication always retains its original order. -/
def jet : List E → (E → A) → E → A
  | [], f => f
  | v::w, f => jet w (directional v f)

def pairs : List E → List (List E × List E)
  | [] => [([],[])]
  | v::w => (pairs w).map (fun p ↦ (v::p.1,p.2)) ++
      (pairs w).map (fun p ↦ (p.1,v::p.2))

theorem directional_smooth {f : E → A} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (directional v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem smooth (w : List E) {f : E → A} {x : E} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (jet w f) x := by
  induction w generalizing f with
  | nil => exact hf
  | cons v w ih => exact ih (directional_smooth hf v)

theorem congr (w : List E) {f g : E → A} {x : E} (hfg : f =ᶠ[𝓝 x] g) : jet w f x = jet w g x := by
  induction w generalizing f g with
  | nil => exact hfg.eq_of_nhds
  | cons v w ih =>
    apply ih
    exact hfg.fderiv.mono fun y hy ↦ congrArg (fun L : E →L[ℝ] A ↦ L v) hy

theorem jet_zero (w : List E) (x : E) : jet w (fun _ : E ↦ (0 : A)) x = 0 := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    have he : directional v (fun _ : E ↦ (0 : A)) = (fun _ ↦ 0) := by
      funext y
      simp only [directional, fderiv_const_apply, ContinuousLinearMap.zero_apply]
    change jet w (directional v (fun _ : E ↦ (0 : A))) x = 0
    rw [he]
    exact ih

theorem jet_const (w : List E) (hw : w≠[]) (C : A) (x : E) : jet w (fun _ : E ↦ C) x = 0 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons v w =>
    have he : directional v (fun _ : E ↦ C) = (fun _ ↦ 0) := by
      funext y
      simp only [directional, fderiv_const_apply, ContinuousLinearMap.zero_apply]
    change jet w (directional v (fun _ : E ↦ C)) x = 0
    rw [he]
    exact jet_zero w x

/-- Exact jets of an affine covariance parameterization: only its first
jet survives. This applies in particular to actual interval masses. -/
theorem affine (v : E) (w : List E) (b : A) (L : E →L[ℝ] A) (x : E) :
    jet (v::w) (fun y ↦ b+L y) x = jet w (fun _ ↦ L v) x := by
  have he : directional v (fun y ↦ b+L y) = (fun _ ↦ L v) := by
    funext y
    change fderiv ℝ (fun z ↦ b+L z) y v = L v
    rw [fderiv_const_add, L.fderiv]
  exact congrArg (fun f : E → A ↦ jet w f x) he

variable (s : Set E) (hs : IsOpen s) (x : E) (hx : x∈s)

include hs hx in
theorem add (w : List E) (f g : E → A)
    (hf : ∀ y∈s, ContDiffAt ℝ ∞ f y) (hg : ∀ y∈s, ContDiffAt ℝ ∞ g y) :
    jet w (fun y ↦ f y+g y) x = jet w f x+jet w g x := by
  induction w generalizing f g with
  | nil => rfl
  | cons v w ih =>
    have he : directional v (fun y ↦ f y+g y) =ᶠ[𝓝 x]
        (fun y ↦ directional v f y+directional v g y) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      simp only [directional, fderiv_fun_add ((hf y hy).differentiableAt (by simp))
        ((hg y hy).differentiableAt (by simp)), ContinuousLinearMap.add_apply]
    exact (congr w he).trans (ih _ _ (fun y hy ↦ directional_smooth (hf y hy) v)
      (fun y hy ↦ directional_smooth (hg y hy) v))

include hs hx in
theorem const_smul (w : List E) (c : ℝ) (f : E → A)
    (hf : ∀ y∈s, ContDiffAt ℝ ∞ f y) :
    jet w (fun y ↦ c • f y) x = c • jet w f x := by
  induction w generalizing f with
  | nil => rfl
  | cons v w ih =>
    have he : directional v (fun y ↦ c • f y) =ᶠ[𝓝 x]
        (fun y ↦ c • directional v f y) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      simp only [directional, fderiv_fun_const_smul ((hf y hy).differentiableAt (by simp)) c,
        ContinuousLinearMap.smul_apply]
    exact (congr w he).trans (ih _ (fun y hy ↦ directional_smooth (hf y hy) v))

end General

section Multiplicative
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
variable (s : Set E) (hs : IsOpen s) (x : E) (hx : x∈s)

include hs hx in
/-- Full mixed Leibniz rule, as a finite list of ordered products.
The list includes every assignment of the differentiation directions
to the two factors, with its proper multiplicity. -/
theorem mul (w : List E) (f g : E → A)
    (hf : ∀ y∈s, ContDiffAt ℝ ∞ f y) (hg : ∀ y∈s, ContDiffAt ℝ ∞ g y) :
    jet w (fun y ↦ f y*g y) x =
      ((pairs w).map (fun p ↦ jet p.1 f x*jet p.2 g x)).sum := by
  induction w generalizing f g with
  | nil => simp only [jet, pairs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | cons v w ih =>
    have he : directional v (fun y ↦ f y*g y) =ᶠ[𝓝 x]
        (fun y ↦ directional v f y*g y+f y*directional v g y) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      simp only [directional, fderiv_fun_mul' ((hf y hy).differentiableAt (by simp))
        ((hg y hy).differentiableAt (by simp)), ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, op_smul_eq_mul, smul_eq_mul]
      exact add_comm _ _
    change jet w (directional v (fun y ↦ f y*g y)) x = _
    calc
      _ = jet w (fun y ↦ directional v f y*g y+f y*directional v g y) x := congr w he
      _ = jet w (fun y ↦ directional v f y*g y) x+jet w (fun y ↦ f y*directional v g y) x :=
        add s hs x hx w _ _
          (fun y hy ↦ (directional_smooth (hf y hy) v).mul (hg y hy))
          (fun y hy ↦ (hf y hy).mul (directional_smooth (hg y hy) v))
      _ = ((pairs w).map (fun p ↦ jet p.1 (directional v f) x*jet p.2 g x)).sum+
          ((pairs w).map (fun p ↦ jet p.1 f x*jet p.2 (directional v g) x)).sum :=
        congrArg₂ (·+·)
          (ih _ _ (fun y hy ↦ directional_smooth (hf y hy) v) hg)
          (ih _ _ hf (fun y hy ↦ directional_smooth (hg y hy) v))
      _ = _ := by simp only [pairs, List.map_append, List.sum_append, List.map_map, Function.comp_def, jet]

end Multiplicative

end SHEStochastic.DirectionalJets
