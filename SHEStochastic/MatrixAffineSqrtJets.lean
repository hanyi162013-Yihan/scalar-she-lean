module

public import SHEStochastic.MatrixMixedJetNorms
public import SHEStochastic.DirectionalJetWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHEStochastic.MatrixAffineSqrtJets
open Matrix DirectionalJets MatrixFrobeniusNorm
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def weight (L : E →L[ℝ] Matrix d d ℝ) (w : List E) : ℝ := (w.map (fun v ↦ size (L v))).prod

theorem weight_nonneg (L : E →L[ℝ] Matrix d d ℝ) (w : List E) : 0≤weight L w := by
  exact List.prod_nonneg (fun x hx ↦ by obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx; exact nonneg _)

/-- A deliberately nonsharp scalar recurrence, uniform in dimension,
base matrix, parameter space and dyadic resolution. -/
def constant (r : ℝ) : ℕ → ℝ
  | 0 => (2*r)⁻¹
  | n+1 => max (constant r n) ((2*r)⁻¹*(1+2^(n+1)*constant r n^2))

theorem constant_nonneg (r : ℝ) (hr : 0≤r) (n : ℕ) : 0≤constant r n := by
  induction n with
  | zero => exact inv_nonneg.mpr (by positivity)
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem constant_mono (r : ℝ) : Monotone (constant r) :=
  monotone_nat_of_le_succ (fun _ ↦ le_max_left _ _)

/-- Affine masses have only a first derivative; the displayed product
also dominates their zero higher jets without a separate case in estimates. -/
theorem affine_bound (b : Matrix d d ℝ) (L : E →L[ℝ] Matrix d d ℝ)
    (w : List E) (hw : w≠[]) (x : E) : size (jet w (fun y ↦ b+L y) x) ≤ weight L w := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons v w =>
    rw [DirectionalJets.affine]
    cases w with
    | nil => simp only [jet, weight, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, le_refl]
    | cons z w =>
      rw [DirectionalJets.jet_const _ (by simp), MatrixFrobeniusNorm.zero]
      exact weight_nonneg L _

/-- Proper mixed products preserve the product of perturbation sizes.
The number of assignments is at most 2 to the total derivative order. -/
theorem proper_bound (L : E →L[ℝ] Matrix d d ℝ) (w : List E) (F G : E → Matrix d d ℝ)
    (x : E) (B : ℝ) (hB : 0≤B)
    (hJets : ∀ p∈properPairs w, size (jet p.1 F x) ≤ B*weight L p.1 ∧
      size (jet p.2 G x) ≤ B*weight L p.2) :
    ((properPairs w).map (fun p ↦ size (jet p.1 F x)*size (jet p.2 G x))).sum ≤
      2^w.length*B^2*weight L w := by
  have he : ∀ p∈properPairs w, size (jet p.1 F x)*size (jet p.2 G x) ≤ B^2*weight L w := by
    intro p hp
    have hh := hJets p hp
    have hpw := pairs_product w (fun v ↦ size (L v)) p (List.mem_filter.mp hp).1
    calc
      _ ≤ (B*weight L p.1)*(B*weight L p.2) :=
        mul_le_mul hh.1 hh.2 (nonneg _) (mul_nonneg hB (weight_nonneg L _))
      _ = B^2*(weight L p.1*weight L p.2) := by ring
      _ = _ := congrArg (fun z : ℝ ↦ B^2*z) hpw
  have hs := sum_map_le (properPairs w) _ (fun _ ↦ B^2*weight L w) he
  have hc : ((properPairs w).length : ℝ) ≤ (2 : ℝ)^w.length := by exact_mod_cast proper_count w
  calc
    _ ≤ ((properPairs w).map (fun _ ↦ B^2*weight L w)).sum := hs
    _ = ((properPairs w).length : ℝ)*(B^2*weight L w) := by simp [List.map_const', nsmul_eq_mul]
    _ ≤ (2 : ℝ)^w.length*(B^2*weight L w) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) (weight_nonneg L _))
    _ = _ := by ring

/-- All actual mixed square-root jets of affine positive covariance
masses satisfy an order-only bound. Ellipticity is imposed at the point;
the positive parameter domain supplies smoothness, not extra jets. -/
theorem bound (b : Matrix d d ℝ) (L : E →L[ℝ] Matrix d d ℝ)
    (s : Set E) (hs : IsOpen s) (hp : ∀ y∈s, (b+L y).PosDef)
    (x : E) (hx : x∈s) (r : ℝ) (hr : 0<r)
    (hLo : r^2 • (1 : Matrix d d ℝ) ≤ b+L x)
    (w : List E) (hw : w≠[]) :
    size (jet w (fun y ↦ CFC.sqrt (b+L y)) x) ≤ constant r w.length*weight L w := by
  have hA : ∀ y∈s, ContDiffAt ℝ ∞ (fun z ↦ b+L z) y :=
    fun y _ ↦ contDiffAt_const.add L.contDiff.contDiffAt
  have hrec : ∀ n : ℕ, ∀ v : List E, v.length=n → v≠[] →
      size (jet v (fun y ↦ CFC.sqrt (b+L y)) x) ≤ constant r n*weight L v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hnv
      cases n with
      | zero => exact (hnv (List.length_eq_zero_iff.mp hv)).elim
      | succ n =>
        have hJ : ∀ p∈properPairs v,
            size (jet p.1 (fun y ↦ CFC.sqrt (b+L y)) x) ≤ constant r n*weight L p.1 ∧
            size (jet p.2 (fun y ↦ CFC.sqrt (b+L y)) x) ≤ constant r n*weight L p.2 := by
          intro p hpv
          have hl := proper_lower v p hpv
          rw [hv] at hl
          have hne1 : p.1≠[] := fun he ↦ by simp only [he, List.length_nil] at hl; omega
          have hne2 : p.2≠[] := fun he ↦ by simp only [he, List.length_nil] at hl; omega
          constructor
          · exact (ih p.1.length hl.2.1 p.1 rfl hne1).trans
              (mul_le_mul_of_nonneg_right (constant_mono r (by omega)) (weight_nonneg L _))
          · exact (ih p.2.length hl.2.2.2 p.2 rfl hne2).trans
              (mul_le_mul_of_nonneg_right (constant_mono r (by omega)) (weight_nonneg L _))
        have hS := MatrixMixedJetNorms.sqrt (fun y ↦ b+L y) s hs hA hp x hx v hnv r hr.le hLo
        have hP := proper_bound L v (fun y ↦ CFC.sqrt (b+L y)) (fun y ↦ CFC.sqrt (b+L y)) x (constant r n) (constant_nonneg r hr.le n) hJ
        have hTot : 2*r*size (jet v (fun y ↦ CFC.sqrt (b+L y)) x) ≤
            (1+2^(n+1)*constant r n^2)*weight L v := by
          have hh := hS.trans (add_le_add (affine_bound b L v hnv x) hP)
          rw [hv] at hh
          nlinarith only [hh]
        have hdiv : size (jet v (fun y ↦ CFC.sqrt (b+L y)) x) ≤
            ((1+2^(n+1)*constant r n^2)*weight L v)/(2*r) :=
          (le_div_iff₀ (by positivity : 0<2*r)).mpr (by nlinarith only [hTot])
        apply hdiv.trans
        rw [div_eq_mul_inv]
        calc
          _ = ((2*r)⁻¹*(1+2^(n+1)*constant r n^2))*weight L v := by ring
          _ ≤ constant r (n+1)*weight L v :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (weight_nonneg L _)
  exact hrec w.length w rfl hw

end SHEStochastic.MatrixAffineSqrtJets
