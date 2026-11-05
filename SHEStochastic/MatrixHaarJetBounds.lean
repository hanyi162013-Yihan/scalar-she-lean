module

public import SHEStochastic.MatrixJetClosure
public import SHEStochastic.MatrixEllipticOrder
public import SHEStochastic.MatrixHaarScaling

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section

namespace SHEStochastic.MatrixHaarJetBounds
open Matrix DirectionalJets MatrixFrobeniusNorm MatrixJetClosure Filter
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff Topology

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def inverseSize (d : Type*) [Fintype d] (m : ℝ) : ℝ := Real.sqrt (Fintype.card d : ℝ)/m
def rootLower (U : ℝ) : ℝ := Real.sqrt (2/U)
def massConstant (d : Type*) [Fintype d] (m : ℝ) : ℕ → ℝ :=
  inverseConstant (inverseSize d m) (fun _ => 1)
def rootConstant (d : Type*) [Fintype d] (m U : ℝ) : ℕ → ℝ :=
  MatrixJetClosure.rootConstant (rootLower U) (fun n => massConstant d m n+massConstant d m n)
def normalizerConstant (d : Type*) [Fintype d] (m U : ℝ) : ℕ → ℝ :=
  inverseConstant (inverseSize d (rootLower U)) (rootConstant d m U)
def childConstant (d : Type*) [Fintype d] (m U : ℝ) (n : ℕ) : ℝ :=
  inverseSize d m*normalizerConstant d m U n+
    massConstant d m n*inverseSize d (rootLower U)+
    2^n*(max (massConstant d m n) (normalizerConstant d m U n))^2

/-- Every actual mixed derivative of the two ordered child coefficients
is controlled by ellipticity, the state dimension and the order. The
common weight records both child perturbations; no grid depth occurs. -/
theorem children (a b : Matrix d d ℝ) (L R : E →L[ℝ] Matrix d d ℝ)
    (s : Set E) (hs : IsOpen s)
    (hp : ∀ y∈s, (a+L y).PosDef ∧ (b+R y).PosDef)
    (x : E) (hx : x∈s) (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hLo : m • (1 : Matrix d d ℝ) ≤ a+L x ∧ m • (1 : Matrix d d ℝ) ≤ b+R x)
    (hHi : a+L x ≤ U • (1 : Matrix d d ℝ) ∧ b+R x ≤ U • (1 : Matrix d d ℝ))
    (w : List E) (hw : w≠[]) :
    size (jet w (fun y => MatrixHaarAlgebra.left (a+L y) (b+R y)) x) ≤
        childConstant d m U w.length*weight (fun v => size (L v)+size (R v)) w ∧
    size (jet w (fun y => MatrixHaarAlgebra.right (a+L y) (b+R y)) x) ≤
        childConstant d m U w.length*weight (fun v => size (L v)+size (R v)) w := by
  let A := fun y => a+L y
  let B := fun y => b+R y
  let S := fun y => (A y)⁻¹+(B y)⁻¹
  let T := fun y => CFC.sqrt (S y)
  let N := fun y => (T y)⁻¹
  let ρ := fun v => size (L v)+size (R v)
  have hρ : ∀ v, 0≤ρ v := fun _ => add_nonneg (nonneg _) (nonneg _)
  have hA : ∀ y∈s, ContDiffAt ℝ ∞ A y := fun _ _ => contDiffAt_const.add L.contDiff.contDiffAt
  have hB : ∀ y∈s, ContDiffAt ℝ ∞ B y := fun _ _ => contDiffAt_const.add R.contDiff.contDiffAt
  have hiA : ∀ y∈s, ContDiffAt ℝ ∞ (fun z => (A z)⁻¹) y :=
    fun y hy => MatrixHaarSmooth.inverse (hA y hy) (hp y hy).1.isUnit
  have hiB : ∀ y∈s, ContDiffAt ℝ ∞ (fun z => (B z)⁻¹) y :=
    fun y hy => MatrixHaarSmooth.inverse (hB y hy) (hp y hy).2.isUnit
  have hpS : ∀ y∈s, (S y).PosDef := fun y hy => (hp y hy).1.inv.add (hp y hy).2.inv
  have hS : ∀ y∈s, ContDiffAt ℝ ∞ S y := fun y hy => (hiA y hy).add (hiB y hy)
  have hT : ∀ y∈s, ContDiffAt ℝ ∞ T y := fun y hy =>
    MatrixSqrtSmooth.comp (hS y hy) (hpS y hy)
      ((show ∀ᶠ z in 𝓝 y, z∈s from hs.mem_nhds hy).mono fun z hz => (hpS z hz).posSemidef.nonneg)
  have hpT : ∀ y∈s, (T y).PosDef := fun y hy => MatrixHaarPositive.sqrt_posDef _ (hpS y hy)
  have hN : ∀ y∈s, ContDiffAt ℝ ∞ N y :=
    fun y hy => MatrixHaarSmooth.inverse (hT y hy) (hpT y hy).isUnit
  have hInvA : size ((A x)⁻¹) ≤ inverseSize d m :=
    MatrixEllipticSize.inverse _ (hp x hx).1 m hm hLo.1
  have hInvB : size ((B x)⁻¹) ≤ inverseSize d m :=
    MatrixEllipticSize.inverse _ (hp x hx).2 m hm hLo.2
  have hJA : ∀ v : List E, v≠[] → size (jet v (fun y => (A y)⁻¹) x) ≤ massConstant d m v.length*weight ρ v := by
    intro v hv
    apply MatrixJetClosure.inverse A ρ hρ (fun _ => 1) (fun _ => zero_le_one) monotone_const
      s hs hA (fun y hy => (hp y hy).1.isUnit) x hx _ hInvA
    · intro z hz
      simpa only [one_mul] using MatrixJetClosure.affine a L ρ hρ
        (fun _ => le_add_of_nonneg_right (nonneg _)) x z hz
    · exact hv
  have hJB : ∀ v : List E, v≠[] → size (jet v (fun y => (B y)⁻¹) x) ≤ massConstant d m v.length*weight ρ v := by
    intro v hv
    apply MatrixJetClosure.inverse B ρ hρ (fun _ => 1) (fun _ => zero_le_one) monotone_const
      s hs hB (fun y hy => (hp y hy).2.isUnit) x hx _ hInvB
    · intro z hz
      simpa only [one_mul] using MatrixJetClosure.affine b R ρ hρ
        (fun _ => le_add_of_nonneg_left (nonneg _)) x z hz
    · exact hv
  have hJS : ∀ v : List E, v≠[] → size (jet v S x) ≤
      (massConstant d m v.length+massConstant d m v.length)*weight ρ v :=
    fun v hv => MatrixJetClosure.sum _ _ s hs hiA hiB x hx ρ _ _ hJA hJB v hv
  have hInvLowerA := (MatrixEllipticOrder.inverse_bounds _ (hp x hx).1 m U hm hLo.1 hHi.1).1
  have hInvLowerB := (MatrixEllipticOrder.inverse_bounds _ (hp x hx).2 m U hm hLo.2 hHi.2).1
  have hr : 0 < rootLower U := Real.sqrt_pos.mpr (div_pos (by norm_num) hU)
  have hLower : (rootLower U)^2 • (1 : Matrix d d ℝ) ≤ S x := by
    have he : U⁻¹+U⁻¹ = (rootLower U)^2 := by
      rw [rootLower, Real.sq_sqrt (div_nonneg (by norm_num) hU.le)]
      ring
    simpa only [← add_smul, he] using add_le_add hInvLowerA hInvLowerB
  have hJN : ∀ v : List E, v≠[] → size (jet v N x) ≤ normalizerConstant d m U v.length*weight ρ v := by
    intro v hv
    apply MatrixJetClosure.inverse T ρ hρ (rootConstant d m U)
      (MatrixJetClosure.rootConstant_nonneg _ _) (MatrixJetClosure.rootConstant_mono _ _)
      s hs hT (fun y hy => (hpT y hy).isUnit) x hx _
      (MatrixEllipticSize.inverse_sqrt _ (hpS x hx) _ hr hLower)
    · intro z hz
      exact MatrixJetClosure.sqrt S ρ hρ _ s hs hS hpS x hx _ hr hLower hJS z hz
    · exact hv
  have hNormN : size (N x) ≤ inverseSize d (rootLower U) :=
    MatrixEllipticSize.inverse_sqrt _ (hpS x hx) _ hr hLower
  have hOutA := MatrixJetClosure.product (fun y => (A y)⁻¹) N s hs hiA hN x hx ρ hρ
    (massConstant d m) (normalizerConstant d m U)
    (inverseConstant_nonneg _ _) (inverseConstant_nonneg _ _)
    (inverseConstant_mono _ _) (inverseConstant_mono _ _)
    _ _ hInvA hNormN hJA hJN w hw
  have hOutB := MatrixJetClosure.product (fun y => (B y)⁻¹) N s hs hiB hN x hx ρ hρ
    (massConstant d m) (normalizerConstant d m U)
    (inverseConstant_nonneg _ _) (inverseConstant_nonneg _ _)
    (inverseConstant_mono _ _) (inverseConstant_mono _ _)
    _ _ hInvB hNormN hJB hJN w hw
  constructor
  · exact hOutA
  · have he := DirectionalJets.const_smul s hs x hx w (-1) (fun y => (B y)⁻¹*N y)
      (fun y hy => (hiB y hy).mul (hN y hy))
    simp only [neg_one_smul] at he
    change size (jet w (fun y => -((B y)⁻¹*N y)) x) ≤ _
    rw [he, MatrixFrobeniusNorm.neg]
    exact hOutB

end SHEStochastic.MatrixHaarJetBounds
