module

public import SHE.HaarRealSpace
public import SHE.RealMultiplier
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.NoiseSplitting
open scoped InnerProductSpace

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual two-channel operator used before the residual Haar rotation. -/
def block (C D : E →L[ℝ] E) : WithLp 2 (E × E) →ₗ[ℝ] WithLp 2 (E × E) where
  toFun p := WithLp.toLp 2 (C p.fst+D p.snd,D p.fst-C p.snd)
  map_add' p q := by
    apply WithLp.ofLp_injective
    ext <;> simp [map_add] <;> abel
  map_smul' r p := by
    apply WithLp.ofLp_injective
    ext <;> simp [map_smul,smul_add,smul_sub]

theorem block_involutive (C D : E →L[ℝ] E)
    (hsum : ∀ x,C (C x)+D (D x)=x) (hcomm : ∀ x,C (D x)=D (C x)) :
    Function.Involutive (block C D) := by
  intro p
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change C (C p.fst+D p.snd)+D (D p.fst-C p.snd)=p.fst
    rw [map_add,map_sub,hcomm]
    calc
      _ = C (C p.fst)+D (D p.fst) := by abel
      _ = _ := hsum p.fst
  · change D (C p.fst+D p.snd)-C (D p.fst-C p.snd)=p.snd
    rw [map_add,map_sub,hcomm]
    calc
      _ = C (C p.snd)+D (D p.snd) := by abel
      _ = _ := hsum p.snd

theorem block_symmetric (C D : E →L[ℝ] E)
    (hC : ∀ x y,⟪C x,y⟫_ℝ=⟪x,C y⟫_ℝ)
    (hD : ∀ x y,⟪D x,y⟫_ℝ=⟪x,D y⟫_ℝ)
    (p q : WithLp 2 (E × E)) :
    ⟪block C D p,q⟫_ℝ=⟪p,block C D q⟫_ℝ := by
  simp only [WithLp.prod_inner_apply]
  change ⟪C p.fst+D p.snd,q.fst⟫_ℝ+⟪D p.fst-C p.snd,q.snd⟫_ℝ =
    ⟪p.fst,C q.fst+D q.snd⟫_ℝ+⟪p.snd,D q.fst-C q.snd⟫_ℝ
  simp only [inner_add_left,inner_sub_left,inner_add_right,inner_sub_right,hC,hD]
  ring

/-- The block is a genuine real Hilbert-space isometry with its own
inverse, including the cross-channel orthogonality needed by the standard
predictable Brownian rotation theorem. -/
def orthogonalBlock (C D : E →L[ℝ] E)
    (hsum : ∀ x,C (C x)+D (D x)=x) (hcomm : ∀ x,C (D x)=D (C x))
    (hC : ∀ x y,⟪C x,y⟫_ℝ=⟪x,C y⟫_ℝ)
    (hD : ∀ x y,⟪D x,y⟫_ℝ=⟪x,D y⟫_ℝ) :
    WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E) :=
  LinearEquiv.isometryOfInner
    { block C D with
      invFun := block C D
      left_inv := block_involutive C D hsum hcomm
      right_inv := block_involutive C D hsum hcomm }
    (fun p q => by
      change ⟪block C D p,block C D q⟫_ℝ=⟪p,q⟫_ℝ
      rw [block_symmetric C D hC hD,block_involutive C D hsum hcomm q])

end Hilbert

open MeasureTheory
open scoped ENNReal

def additiveRatio (m g : ℝ) : ℝ := m/g
def residualRatio (m g : ℝ) : ℝ := Real.sqrt (g^2-m^2)/g

theorem splitting_scalar {m g : ℝ} (hm : 0 < m) (hg : m ≤ |g|) :
    (additiveRatio m g)^2+(residualRatio m g)^2=1 ∧
    |additiveRatio m g| ≤ 1 ∧ |residualRatio m g| ≤ 1 ∧
    m*additiveRatio m g+Real.sqrt (g^2-m^2)*residualRatio m g=g ∧
    m*residualRatio m g-Real.sqrt (g^2-m^2)*additiveRatio m g=0 := by
  have hg0 : g ≠ 0 := abs_pos.mp (hm.trans_le hg)
  have hr : 0 ≤ g^2-m^2 := by nlinarith [sq_abs g]
  have hs := Real.sq_sqrt hr
  have hu : (additiveRatio m g)^2+(residualRatio m g)^2=1 := by
    unfold additiveRatio residualRatio
    field_simp
    nlinarith only [hs]
  refine ⟨hu,?_,?_,?_,?_⟩
  · have hh := sq_nonneg (residualRatio m g)
    nlinarith [sq_abs (additiveRatio m g),abs_nonneg (additiveRatio m g)]
  · have hh := sq_nonneg (additiveRatio m g)
    nlinarith [sq_abs (residualRatio m g),abs_nonneg (residualRatio m g)]
  · unfold additiveRatio residualRatio
    field_simp
    nlinarith only [hs]
  · unfold additiveRatio residualRatio
    ring

section Physical
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable (g : X → ℝ) (hg : AEStronglyMeasurable g μ) (m : ℝ) (hm : 0 < m)
variable (hgap : ∀ᵐ x ∂μ,m ≤ |g x|)

include hg in
theorem additiveRatio_measurable : AEStronglyMeasurable (fun x => additiveRatio m (g x)) μ :=
  aestronglyMeasurable_const.div₀ hg

include hg in
theorem residualRatio_measurable : AEStronglyMeasurable (fun x => residualRatio m (g x)) μ := by
  exact (Real.continuous_sqrt.comp_aestronglyMeasurable
    ((hg.pow 2).sub aestronglyMeasurable_const)).div₀ hg

include hm hgap in
theorem additiveRatio_bound : ∀ᵐ x ∂μ,‖additiveRatio m (g x)‖ ≤ 1 := by
  filter_upwards [hgap] with x hx
  exact (splitting_scalar hm hx).2.1

include hm hgap in
theorem residualRatio_bound : ∀ᵐ x ∂μ,‖residualRatio m (g x)‖ ≤ 1 := by
  filter_upwards [hgap] with x hx
  exact (splitting_scalar hm hx).2.2.1

def additiveOperator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  RealMultiplier.operator μ _ (additiveRatio_measurable μ g hg m) 1
    (additiveRatio_bound μ g m hm hgap)

def residualOperator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  RealMultiplier.operator μ _ (residualRatio_measurable μ g hg m) 1
    (residualRatio_bound μ g m hm hgap)

/-- The literal physical two-noise splitting is orthogonal on real
`L² ⊕ L²`. This theorem permits either sign of the original coefficient. -/
def physicalRotation : WithLp 2 (Lp ℝ 2 μ × Lp ℝ 2 μ) ≃ₗᵢ[ℝ]
    WithLp 2 (Lp ℝ 2 μ × Lp ℝ 2 μ) :=
  orthogonalBlock (additiveOperator μ g hg m hm hgap) (residualOperator μ g hg m hm hgap)
    (RealMultiplier.operator_sum_squares μ _ _ _ _ 1 1 _ _ (by
      filter_upwards [hgap] with x hx
      exact (splitting_scalar hm hx).1))
    (RealMultiplier.operator_commute μ _ _ _ _ 1 1 _ _)
    (RealMultiplier.operator_symmetric μ _ _ 1 _)
    (RealMultiplier.operator_symmetric μ _ _ 1 _)

theorem physicalRotation_ae (p : WithLp 2 (Lp ℝ 2 μ × Lp ℝ 2 μ)) :
    ∀ᵐ x ∂μ,
      (physicalRotation μ g hg m hm hgap p).fst x=
        additiveRatio m (g x)*p.fst x+residualRatio m (g x)*p.snd x ∧
      (physicalRotation μ g hg m hm hgap p).snd x=
        residualRatio m (g x)*p.fst x-additiveRatio m (g x)*p.snd x := by
  let C := additiveOperator μ g hg m hm hgap
  let D := residualOperator μ g hg m hm hgap
  change ∀ᵐ x ∂μ,(C p.fst+D p.snd) x=_ ∧ (D p.fst-C p.snd) x=_
  filter_upwards [RealMultiplier.operator_ae μ _ _ 1 _ p.fst,
    RealMultiplier.operator_ae μ _ _ 1 _ p.snd,
    RealMultiplier.operator_ae μ _ _ 1 _ p.fst,
    RealMultiplier.operator_ae μ _ _ 1 _ p.snd,
    Lp.coeFn_add (C p.fst) (D p.snd),Lp.coeFn_sub (D p.fst) (C p.snd)] with x hc hd he hf ha hs
  constructor
  · rw [ha]
    exact congrArg₂ (·+·) hc hd
  · rw [hs]
    exact congrArg₂ (·-·) he hf

theorem physical_reconstruction_ae (p : WithLp 2 (Lp ℝ 2 μ × Lp ℝ 2 μ)) :
    ∀ᵐ x ∂μ,m*(physicalRotation μ g hg m hm hgap p).fst x+
      Real.sqrt ((g x)^2-m^2)*(physicalRotation μ g hg m hm hgap p).snd x=g x*p.fst x := by
  filter_upwards [physicalRotation_ae μ g hg m hm hgap p,hgap] with x hp hx
  rw [hp.1,hp.2]
  obtain ⟨_,_,_,hfirst,hsecond⟩ := splitting_scalar hm hx
  calc
    _ = (m*additiveRatio m (g x)+Real.sqrt ((g x)^2-m^2)*residualRatio m (g x))*p.fst x+
      (m*residualRatio m (g x)-Real.sqrt ((g x)^2-m^2)*additiveRatio m (g x))*p.snd x := by ring
    _ = _ := by rw [hfirst,hsecond,zero_mul,add_zero]

theorem physicalRotation_involutive : Function.Involutive (physicalRotation μ g hg m hm hgap) := by
  exact block_involutive _ _
    (RealMultiplier.operator_sum_squares μ _ _ _ _ 1 1 _ _ (by
      filter_upwards [hgap] with x hx
      exact (splitting_scalar hm hx).1))
    (RealMultiplier.operator_commute μ _ _ _ _ 1 1 _ _)

end Physical
end SHE.NoiseSplitting
