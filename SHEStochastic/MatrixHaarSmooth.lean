module

public import SHEStochastic.MatrixSqrtSmooth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixHaarSmooth
open Matrix Filter MatrixHaarAlgebra SHE.FiniteHaar
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : WithTop ℕ∞} {x : E}

/-- The total nonsingular inverse is smooth at each invertible matrix. -/
theorem inverse {g : E → Matrix d d ℝ} (hg : ContDiffAt ℝ k g x) (hu : IsUnit (g x)) :
    ContDiffAt ℝ k (fun y ↦ (g y)⁻¹) x := by
  have hi : ContDiffAt ℝ k Ring.inverse (g x) := by
    simpa only [hu.unit_spec] using contDiffAt_ringInverse ℝ hu.unit
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse] using hi.comp x hg

/-- The ordered two-child coefficients have derivatives of every order
along any smooth positive definite mass parameterization. -/
theorem children {A B : E → Matrix d d ℝ}
    (hA : ContDiffAt ℝ k A x) (hB : ContDiffAt ℝ k B x)
    (hpA : (A x).PosDef) (hpB : (B x).PosDef)
    (he : ∀ᶠ y in 𝓝 x, (A y).PosDef ∧ (B y).PosDef) :
    ContDiffAt ℝ k (fun y ↦ left (A y) (B y)) x ∧
      ContDiffAt ℝ k (fun y ↦ right (A y) (B y)) x := by
  have hiA := inverse hA hpA.isUnit
  have hiB := inverse hB hpB.isUnit
  have hsum := hiA.add hiB
  have hroot := MatrixSqrtSmooth.comp hsum (hpA.inv.add hpB.inv)
    (he.mono fun y hy ↦ (hy.1.inv.add hy.2.inv).posSemidef.nonneg)
  have hn := inverse hroot (MatrixHaarPositive.sqrt_posDef _ (hpA.inv.add hpB.inv)).isUnit
  exact ⟨hiA.mul hn, (hiB.mul hn).neg⟩

theorem totalMass (n : ℕ) (κ : E → Grid n → Matrix d d ℝ)
    (hc : ∀ y, ContDiffAt ℝ k (fun z ↦ κ z y) x) :
    ContDiffAt ℝ k (fun z ↦ MatrixFiniteHaar.totalMass n (κ z)) x := by
  exact ContDiffAt.sum (fun y _ ↦ hc y)

/-- All finite matrix Haar detail columns are smooth in the actual leaf
covariances. The proof follows the existing binary tree without adding
independent derivative data. -/
theorem detailColumn (n : ℕ) (κ : E → Grid n → Matrix d d ℝ)
    (hc : ∀ y, ContDiffAt ℝ k (fun z ↦ κ z y) x)
    (hp : ∀ y, (κ x y).PosDef)
    (he : ∀ᶠ z in 𝓝 x, ∀ y, (κ z y).PosDef)
    (i : DetailIndex n) (y : Grid n) :
    ContDiffAt ℝ k (fun z ↦ MatrixFiniteHaar.detailColumn n (κ z) i y) x := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    dsimp only [Grid, DetailIndex, gridFintype, detailFintype] at κ hc hp he i y ⊢
    have hcl := totalMass n (fun z t ↦ κ z (Sum.inl t)) (fun t ↦ hc (Sum.inl t))
    have hcr := totalMass n (fun z t ↦ κ z (Sum.inr t)) (fun t ↦ hc (Sum.inr t))
    have hpl := MatrixFiniteHaar.totalMass_posDef n (fun t ↦ κ x (Sum.inl t)) (fun t ↦ hp (Sum.inl t))
    have hpr := MatrixFiniteHaar.totalMass_posDef n (fun t ↦ κ x (Sum.inr t)) (fun t ↦ hp (Sum.inr t))
    have hem : ∀ᶠ z in 𝓝 x,
        (MatrixFiniteHaar.totalMass n (fun t ↦ κ z (Sum.inl t))).PosDef ∧
        (MatrixFiniteHaar.totalMass n (fun t ↦ κ z (Sum.inr t))).PosDef := he.mono fun z hz ↦
      ⟨MatrixFiniteHaar.totalMass_posDef n _ (fun t ↦ hz (Sum.inl t)),
        MatrixFiniteHaar.totalMass_posDef n _ (fun t ↦ hz (Sum.inr t))⟩
    rcases i with ⟨⟩ | (i | i) <;> rcases y with y | y
    · exact (children hcl hcr hpl hpr hem).1
    · exact (children hcl hcr hpl hpr hem).2
    · exact ih (fun z t ↦ κ z (Sum.inl t)) (fun t ↦ hc (Sum.inl t))
        (fun t ↦ hp (Sum.inl t)) (he.mono fun z hz t ↦ hz (Sum.inl t)) i y
    · exact contDiffAt_const
    · exact contDiffAt_const
    · exact ih (fun z t ↦ κ z (Sum.inr t)) (fun t ↦ hc (Sum.inr t))
        (fun t ↦ hp (Sum.inr t)) (he.mono fun z hz t ↦ hz (Sum.inr t)) i y

theorem inverseSqrt {A : E → Matrix d d ℝ} (hA : ContDiffAt ℝ k A x)
    (hp : (A x).PosDef) (he : ∀ᶠ y in 𝓝 x, (A y).PosDef) :
    ContDiffAt ℝ k (fun y ↦ MatrixFiniteHaar.inverseSqrt (A y)) x := by
  have hr := MatrixSqrtSmooth.comp hA hp (he.mono fun y hy ↦ hy.posSemidef.nonneg)
  exact inverse hr (MatrixHaarPositive.sqrt_posDef _ hp).isUnit

theorem haarColumn (n : ℕ) (κ : E → Grid n → Matrix d d ℝ)
    (hc : ∀ y, ContDiffAt ℝ k (fun z ↦ κ z y) x)
    (hp : ∀ y, (κ x y).PosDef)
    (he : ∀ᶠ z in 𝓝 x, ∀ y, (κ z y).PosDef)
    (i : Option (DetailIndex n)) (y : Grid n) :
    ContDiffAt ℝ k (fun z ↦ MatrixFiniteHaar.haarColumn n (κ z) i y) x := by
  cases i with
  | none =>
    exact inverseSqrt (totalMass n κ hc) (MatrixFiniteHaar.totalMass_posDef n (κ x) hp)
      (he.mono fun z hz ↦ MatrixFiniteHaar.totalMass_posDef n (κ z) hz)
  | some i => exact detailColumn n κ hc hp he i y

end SHEStochastic.MatrixHaarSmooth
