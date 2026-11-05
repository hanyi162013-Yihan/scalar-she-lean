module

public import SHEStochastic.MatrixAffineSqrtJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHEStochastic.MatrixJetClosure
open Matrix DirectionalJets MatrixFrobeniusNorm
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common perturbation weight may control both child mass maps. -/
def weight (ρ : E → ℝ) (w : List E) : ℝ := (w.map ρ).prod

theorem weight_nonneg (ρ : E → ℝ) (hρ : ∀ v, 0≤ρ v) (w : List E) : 0≤ weight ρ w := by
  exact List.prod_nonneg (fun z hz ↦ by obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz; exact hρ v)

theorem proper_bound (ρ : E → ℝ) (hρ : ∀ v, 0≤ρ v) (w : List E) (F G : E → Matrix d d ℝ)
    (x : E) (B : ℝ) (hB : 0≤ B)
    (hJets : ∀ p∈properPairs w, size (jet p.1 F x) ≤ B*weight ρ p.1 ∧
      size (jet p.2 G x) ≤ B*weight ρ p.2) :
    ((properPairs w).map (fun p ↦ size (jet p.1 F x)*size (jet p.2 G x))).sum ≤
      2^w.length*B^2*weight ρ w := by
  have he : ∀ p∈properPairs w, size (jet p.1 F x)*size (jet p.2 G x) ≤ B^2*weight ρ w := by
    intro p hp
    have hh := hJets p hp
    have hpw := pairs_product w ρ p (List.mem_filter.mp hp).1
    calc
      _ ≤ (B*weight ρ p.1)*(B*weight ρ p.2) :=
        mul_le_mul hh.1 hh.2 (nonneg _) (mul_nonneg hB (weight_nonneg ρ hρ _))
      _ = B^2*(weight ρ p.1*weight ρ p.2) := by ring
      _ = _ := congrArg (fun z : ℝ ↦ B^2*z) hpw
  have hs := sum_map_le (properPairs w) _ (fun _ ↦ B^2*weight ρ w) he
  have hc : ((properPairs w).length : ℝ) ≤ (2 : ℝ)^w.length := by exact_mod_cast proper_count w
  calc
    _ ≤ ((properPairs w).map (fun _ ↦ B^2*weight ρ w)).sum := hs
    _ = ((properPairs w).length : ℝ)*(B^2*weight ρ w) := by simp [List.map_const', nsmul_eq_mul]
    _ ≤ (2 : ℝ)^w.length*(B^2*weight ρ w) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) (weight_nonneg ρ hρ _))
    _ = _ := by ring

def rootConstant (r : ℝ) (M : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => max (rootConstant r M n) ((2*r)⁻¹*(M (n+1)+2^(n+1)*rootConstant r M n^2))

theorem rootConstant_nonneg (r : ℝ) (M : ℕ → ℝ) (n : ℕ) : 0≤ rootConstant r M n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem rootConstant_mono (r : ℝ) (M : ℕ → ℝ) : Monotone (rootConstant r M) :=
  monotone_nat_of_le_succ (fun _ ↦ le_max_left _ _)

/-- All mixed square-root estimates propagate through a genuinely
nonlinear positive matrix map. Only its already proved input bounds
and ellipticity enter the order-dependent constants. -/
theorem sqrt (A : E → Matrix d d ℝ) (ρ : E → ℝ) (hρ : ∀ v, 0≤ρ v)
    (M : ℕ → ℝ)
    (s : Set E) (hs : IsOpen s) (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hp : ∀ y∈s, (A y).PosDef)
    (x : E) (hx : x∈s) (r : ℝ) (hr : 0< r)
    (hLo : r^2 • (1 : Matrix d d ℝ) ≤ A x)
    (hInput : ∀ w : List E, w≠[] → size (jet w A x) ≤ M w.length*weight ρ w)
    (w : List E) (hw : w≠[]) :
    size (jet w (fun y ↦ CFC.sqrt (A y)) x) ≤ rootConstant r M w.length*weight ρ w := by
  have hrec : ∀ n : ℕ, ∀ v : List E, v.length=n → v≠[] →
      size (jet v (fun y ↦ CFC.sqrt (A y)) x) ≤ rootConstant r M n*weight ρ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hnv
      cases n with
      | zero => exact (hnv (List.length_eq_zero_iff.mp hv)).elim
      | succ n =>
        have hJ : ∀ p∈properPairs v,
            size (jet p.1 (fun y ↦ CFC.sqrt (A y)) x) ≤ rootConstant r M n*weight ρ p.1 ∧
            size (jet p.2 (fun y ↦ CFC.sqrt (A y)) x) ≤ rootConstant r M n*weight ρ p.2 := by
          intro p hpv
          have hl := proper_lower v p hpv
          rw [hv] at hl
          have hne1 : p.1≠[] := fun he ↦ by simp only [he, List.length_nil] at hl; omega
          have hne2 : p.2≠[] := fun he ↦ by simp only [he, List.length_nil] at hl; omega
          constructor
          · exact (ih p.1.length hl.2.1 p.1 rfl hne1).trans
              (mul_le_mul_of_nonneg_right (rootConstant_mono r M (by omega)) (weight_nonneg ρ hρ _))
          · exact (ih p.2.length hl.2.2.2 p.2 rfl hne2).trans
              (mul_le_mul_of_nonneg_right (rootConstant_mono r M (by omega)) (weight_nonneg ρ hρ _))
        have hS := MatrixMixedJetNorms.sqrt A s hs hA hp x hx v hnv r hr.le hLo
        have hP := proper_bound ρ hρ v (fun y ↦ CFC.sqrt (A y)) (fun y ↦ CFC.sqrt (A y)) x (rootConstant r M n) (rootConstant_nonneg r M n) hJ
        have hTot : 2*r*size (jet v (fun y ↦ CFC.sqrt (A y)) x) ≤
            (M (n+1)+2^(n+1)*rootConstant r M n^2)*weight ρ v := by
          have hh := hS.trans (add_le_add (hInput v hnv) hP)
          rw [hv] at hh
          nlinarith only [hh]
        have hdiv : size (jet v (fun y ↦ CFC.sqrt (A y)) x) ≤
            ((M (n+1)+2^(n+1)*rootConstant r M n^2)*weight ρ v)/(2*r) :=
          (le_div_iff₀ (by positivity : 0<2*r)).mpr (by nlinarith only [hTot])
        apply hdiv.trans
        rw [div_eq_mul_inv]
        calc
          _ = ((2*r)⁻¹*(M (n+1)+2^(n+1)*rootConstant r M n^2))*weight ρ v := by ring
          _ ≤ rootConstant r M (n+1)*weight ρ v :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (weight_nonneg ρ hρ _)
  exact hrec w.length w rfl hw


def inverseConstant (B : ℝ) (M : ℕ → ℝ) : ℕ → ℝ
  | 0 => max 1 (M 0)
  | n+1 => max (inverseConstant B M n)
      (max (M (n+1)) (B*(M (n+1)*B+2^(n+1)*inverseConstant B M n^2)))

theorem inverseConstant_mono (B : ℝ) (M : ℕ → ℝ) : Monotone (inverseConstant B M) :=
  monotone_nat_of_le_succ (fun _ ↦ le_max_left _ _)

theorem input_le_inverseConstant (B : ℝ) (M : ℕ → ℝ) (n : ℕ) : M n≤ inverseConstant B M n := by
  cases n with
  | zero => exact le_max_right _ _
  | succ n => exact (le_max_left _ _).trans (le_max_right _ _)

theorem inverseConstant_nonneg (B : ℝ) (M : ℕ → ℝ) (n : ℕ) : 0≤ inverseConstant B M n :=
  (zero_le_one.trans (le_max_left _ _)).trans (inverseConstant_mono B M (Nat.zero_le n))

/-- All mixed inverse estimates close under nonlinear matrix maps,
with an explicit order-only recurrence and a bound for the actual inverse. -/
theorem inverse (A : E → Matrix d d ℝ) (ρ : E → ℝ) (hρ : ∀ v, 0≤ρ v)
    (M : ℕ → ℝ) (hM : ∀ n, 0≤ M n) (hMono : Monotone M)
    (s : Set E) (hs : IsOpen s) (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hu : ∀ y∈s, IsUnit (A y))
    (x : E) (hx : x∈s) (B : ℝ) (hInv : size ((A x)⁻¹)≤ B)
    (hInput : ∀ w : List E, w≠[] → size (jet w A x) ≤ M w.length*weight ρ w)
    (w : List E) (hw : w≠[]) :
    size (jet w (fun y ↦ (A y)⁻¹) x) ≤ inverseConstant B M w.length*weight ρ w := by
  have hB : 0≤ B := (nonneg _).trans hInv
  have hrec : ∀ n : ℕ, ∀ v : List E, v.length=n → v≠[] →
      size (jet v (fun y ↦ (A y)⁻¹) x) ≤ inverseConstant B M n*weight ρ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hnv
      cases n with
      | zero => exact (hnv (List.length_eq_zero_iff.mp hv)).elim
      | succ n =>
        have hC : 0≤ inverseConstant B M n := inverseConstant_nonneg B M n
        have hJ : ∀ p∈properPairs v,
            size (jet p.1 A x) ≤ inverseConstant B M n*weight ρ p.1 ∧
            size (jet p.2 (fun y ↦ (A y)⁻¹) x) ≤ inverseConstant B M n*weight ρ p.2 := by
          intro p hpv
          have hl := proper_lower v p hpv
          rw [hv] at hl
          have hne1 : p.1≠[] := fun he ↦ by simp only [he, List.length_nil] at hl; omega
          have hne2 : p.2≠[] := fun he ↦ by simp only [he, List.length_nil] at hl; omega
          constructor
          · exact (hInput p.1 hne1).trans
              (mul_le_mul_of_nonneg_right
                ((hMono (by omega : p.1.length≤ n)).trans (input_le_inverseConstant B M n))
                (weight_nonneg ρ hρ p.1))
          · exact (ih p.2.length hl.2.2.2 p.2 rfl hne2).trans
              (mul_le_mul_of_nonneg_right (inverseConstant_mono B M (by omega)) (weight_nonneg ρ hρ _))
        have hP := proper_bound ρ hρ v A (fun y ↦ (A y)⁻¹) x (inverseConstant B M n) hC hJ
        have hI := MatrixMixedJetNorms.inverse A s hs hA hu x hx v hnv
        have hFirst : size (jet v A x)*size ((A x)⁻¹) ≤ M v.length*weight ρ v*B :=
          mul_le_mul (hInput v hnv) hInv (nonneg _) (mul_nonneg (hM _) (weight_nonneg ρ hρ v))
        have hInner := add_le_add hFirst hP
        have hWeight := weight_nonneg ρ hρ v
        have hMv := hM v.length
        have hInnerNonneg : 0≤ M v.length*weight ρ v*B+2^v.length*inverseConstant B M n^2*weight ρ v := by
          positivity
        have hTot : size (jet v (fun y ↦ (A y)⁻¹) x) ≤
            B*(M v.length*weight ρ v*B+2^v.length*inverseConstant B M n^2*weight ρ v) :=
          hI.trans ((mul_le_mul_of_nonneg_left hInner (nonneg _)).trans
            (mul_le_mul_of_nonneg_right hInv hInnerNonneg))
        rw [hv] at hTot
        apply hTot.trans
        calc
          _ = (B*(M (n+1)*B+2^(n+1)*inverseConstant B M n^2))*weight ρ v := by ring
          _ ≤ inverseConstant B M (n+1)*weight ρ v :=
            mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (weight_nonneg ρ hρ _)
  exact hrec w.length w rfl hw


/-- Addition preserves the same common perturbation weight. -/
theorem sum (A B : E → Matrix d d ℝ) (s : Set E) (hs : IsOpen s)
    (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hB : ∀ y∈s, ContDiffAt ℝ ∞ B y)
    (x : E) (hx : x∈s) (ρ : E → ℝ) (M N : ℕ → ℝ)
    (hJA : ∀ w : List E, w≠[] → size (jet w A x) ≤ M w.length*weight ρ w)
    (hJB : ∀ w : List E, w≠[] → size (jet w B x) ≤ N w.length*weight ρ w)
    (w : List E) (hw : w≠[]) :
    size (jet w (fun y => A y+B y) x) ≤ (M w.length+N w.length)*weight ρ w := by
  rw [DirectionalJets.add s hs x hx w A B hA hB]
  exact (MatrixFrobeniusNorm.add _ _).trans ((add_le_add (hJA w hw) (hJB w hw)).trans_eq (by ring))

/-- The mixed product bound separates the two actual zeroth-order
factors from strictly lower mixed terms. -/
theorem product (A B : E → Matrix d d ℝ) (s : Set E) (hs : IsOpen s)
    (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hB : ∀ y∈s, ContDiffAt ℝ ∞ B y)
    (x : E) (hx : x∈s) (ρ : E → ℝ) (hρ : ∀ v, 0≤ρ v)
    (M N : ℕ → ℝ) (hM : ∀ n, 0≤M n) (hN : ∀ n, 0≤N n)
    (hm : Monotone M) (hn : Monotone N) (P Q : ℝ)
    (hP : size (A x)≤ P) (hQ : size (B x)≤ Q)
    (hJA : ∀ w : List E, w≠[] → size (jet w A x) ≤ M w.length*weight ρ w)
    (hJB : ∀ w : List E, w≠[] → size (jet w B x) ≤ N w.length*weight ρ w)
    (w : List E) (hw : w≠[]) :
    size (jet w (fun y => A y*B y) x) ≤
      (P*N w.length+M w.length*Q+2^w.length*(max (M w.length) (N w.length))^2)*weight ρ w := by
  have hC : 0≤max (M w.length) (N w.length) := (hM _).trans (le_max_left _ _)
  have hProper := proper_bound ρ hρ w A B x (max (M w.length) (N w.length)) hC (by
    intro p hp
    have hl := proper_lower w p hp
    have h1 : p.1≠[] := fun he => by simp only [he, List.length_nil] at hl; omega
    have h2 : p.2≠[] := fun he => by simp only [he, List.length_nil] at hl; omega
    exact ⟨(hJA p.1 h1).trans (mul_le_mul_of_nonneg_right
      ((hm hl.2.1.le).trans (le_max_left _ _)) (weight_nonneg ρ hρ _)),
      (hJB p.2 h2).trans (mul_le_mul_of_nonneg_right
        ((hn hl.2.2.2.le).trans (le_max_right _ _)) (weight_nonneg ρ hρ _))⟩)
  have ha : size (A x)*size (jet w B x) ≤ P*(N w.length*weight ρ w) :=
    mul_le_mul hP (hJB w hw) (nonneg _) ((nonneg _).trans hP)
  have hb : size (jet w A x)*size (B x) ≤ (M w.length*weight ρ w)*Q :=
    mul_le_mul (hJA w hw) hQ (nonneg _) (mul_nonneg (hM _) (weight_nonneg ρ hρ _))
  have hh := MatrixMixedJetNorms.product s hs x hx w A B hA hB
  rw [sum_pairs_split w hw] at hh
  change size (jet w (fun y => A y*B y) x) ≤ _ at hh
  exact hh.trans ((add_le_add (add_le_add ha hb) hProper).trans_eq (by ring))


/-- One common weight can dominate several different affine mass maps. -/
theorem affine (b : Matrix d d ℝ) (L : E →L[ℝ] Matrix d d ℝ)
    (ρ : E → ℝ) (hρ : ∀ v, 0≤ρ v) (hL : ∀ v, size (L v)≤ρ v)
    (x : E) (w : List E) (hw : w≠[]) : size (jet w (fun y => b+L y) x) ≤ weight ρ w := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons v w =>
    rw [DirectionalJets.affine]
    cases w with
    | nil => simpa only [jet, weight, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one] using hL v
    | cons z w =>
      rw [DirectionalJets.jet_const _ (by simp), MatrixFrobeniusNorm.zero]
      exact weight_nonneg ρ hρ _

end SHEStochastic.MatrixJetClosure
