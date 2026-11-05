module

public import SHEStochastic.MatrixPhysicalColumnSmooth
public import SHEStochastic.MatrixHaarNormalizedJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixActualColumnCalculus
open MeasureTheory Matrix MatrixInfiniteHaar MatrixPhysicalColumnSmooth
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

def childLength (p : List Bool) : ℝ := (((2^(p.length+1) : ℕ) : ℝ))⁻¹

theorem childLength_pos (p : List Bool) : 0 < childLength p := by unfold childLength; positivity

def normalizedMass (p : List Bool) (b : Bool) : Domain (d := d) →L[ℝ] Matrix d d ℝ :=
  (childLength p)⁻¹ • mass (MatrixGlobalHaar.child p b)

theorem child_mass (P : Profile d) (p : List Bool) (b : Bool) :
    mass (MatrixGlobalHaar.child p b) (MatrixProfileSymmetry.realize d P)=
      MatrixDyadicMass.profile P.value (p.length+1) (SHE.FiniteHaar.bottomLeaf p b) :=
  MatrixProfileHilbert.mass_realize d P (MatrixGlobalHaar.child p b)

theorem child_lower (P : Profile d) (p : List Bool) (b : Bool) :
    (childLength p*P.lower) • (1 : Matrix d d ℝ) ≤
      mass (MatrixGlobalHaar.child p b) (MatrixProfileSymmetry.realize d P) := by
  rw [child_mass]
  exact MatrixDyadicMass.lower P.value P.integrable P.lower P.lower_bound _ _

theorem child_positive (P : Profile d) (p : List Bool) (b : Bool) :
    (mass (MatrixGlobalHaar.child p b) (MatrixProfileSymmetry.realize d P)).PosDef := by
  rw [child_mass]
  exact MatrixDyadicMass.positive P.value P.integrable P.lower P.lower_pos P.lower_bound _ _

theorem normalized_child (P : Profile d) (p : List Bool) (b : Bool) :
    normalizedMass p b (MatrixProfileSymmetry.realize d P)=
      MatrixDyadicMass.average P.value (p.length+1) (SHE.FiniteHaar.bottomLeaf p b) := by
  change (childLength p)⁻¹ • mass (MatrixGlobalHaar.child p b) (MatrixProfileSymmetry.realize d P)=_
  rw [child_mass]
  simp only [childLength, inv_inv, MatrixDyadicMass.average]

/-- Genuine smooth local extension of every actual countable physical
matrix Haar detail column. All mass positivity is derived from the
original bounded elliptic covariance profile. -/
theorem smooth (P : Profile d) (p : List Bool) (i : d) :
    ContDiffAt ℝ ∞ (fun z : Domain (d := d) =>
      MatrixPhysicalColumnMap.detail (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child p true)
        (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i z.val)
      (MatrixProfileSymmetry.realize d P) := by
  have hm := mul_pos (childLength_pos p) P.lower_pos
  exact detail_contDiff _ _ _ _ i _ _ (child_positive P p false) (child_positive P p true)
    ⟨child_lower P p false, child_lower P p true⟩ _ (neighborhood_self _ _ _ _ hm)

/-- Normalized all-order child coefficient bounds on the actual
infinite-dimensional symmetric profile space. The constant is
independent of the dyadic generation; interval length is explicit. -/
theorem coefficient_jets (P : Profile d) (p : List Bool) (w : List (Domain (d := d))) (hw : w≠[]) :
    MatrixFrobeniusNorm.size (DirectionalJets.jet w (fun z => MatrixHaarAlgebra.left
      (mass (MatrixGlobalHaar.child p false) z) (mass (MatrixGlobalHaar.child p true) z))
      (MatrixProfileSymmetry.realize d P)) ≤
      (Real.sqrt (childLength p))⁻¹*(MatrixHaarJetBounds.childConstant d P.lower P.upper w.length*
        MatrixJetClosure.weight (fun v => MatrixFrobeniusNorm.size (normalizedMass p false v)+
          MatrixFrobeniusNorm.size (normalizedMass p true v)) w) ∧
    MatrixFrobeniusNorm.size (DirectionalJets.jet w (fun z => MatrixHaarAlgebra.right
      (mass (MatrixGlobalHaar.child p false) z) (mass (MatrixGlobalHaar.child p true) z))
      (MatrixProfileSymmetry.realize d P)) ≤
      (Real.sqrt (childLength p))⁻¹*(MatrixHaarJetBounds.childConstant d P.lower P.upper w.length*
        MatrixJetClosure.weight (fun v => MatrixFrobeniusNorm.size (normalizedMass p false v)+
          MatrixFrobeniusNorm.size (normalizedMass p true v)) w) := by
  let s := MatrixGlobalHaar.child p false
  let t := MatrixGlobalHaar.child p true
  let x := MatrixProfileSymmetry.realize d P
  let c := childLength p
  let o := neighborhood s t x (c*P.lower)
  have hc : 0 < c := childLength_pos p
  have hm : 0 < c*P.lower := mul_pos hc P.lower_pos
  have ho := neighborhood_open s t x (c*P.lower)
  have hx := neighborhood_self s t x (c*P.lower) hm
  have hp := neighborhood_positive s t x (c*P.lower) (child_positive P p false)
    (child_positive P p true) ⟨child_lower P p false, child_lower P p true⟩
  have hNorm : ∀ y∈o, (0+normalizedMass p false y).PosDef ∧ (0+normalizedMass p true y).PosDef := by
    intro y hy
    constructor
    · rw [zero_add]
      change (c⁻¹ • mass s y).PosDef
      exact (hp y hy).1.smul (inv_pos.mpr hc)
    · rw [zero_add]
      change (c⁻¹ • mass t y).PosDef
      exact (hp y hy).2.smul (inv_pos.mpr hc)
  have hLo (b : Bool) : P.lower • (1 : Matrix d d ℝ) ≤ 0+normalizedMass p b x := by
    rw [zero_add, normalized_child]
    exact MatrixDyadicMass.average_lower P.value P.integrable P.lower P.lower_bound _ _
  have hHi (b : Bool) : 0+normalizedMass p b x ≤ P.upper • (1 : Matrix d d ℝ) := by
    rw [zero_add, normalized_child]
    exact MatrixDyadicMass.average_upper P.value P.integrable P.upper P.upper_bound _ _
  have hh := MatrixHaarNormalizedJets.children 0 0 (normalizedMass p false) (normalizedMass p true)
    o ho hNorm x hx P.lower P.upper P.lower_pos P.upper_pos ⟨hLo false, hLo true⟩ ⟨hHi false, hHi true⟩
    c hc w hw
  have he (b : Bool) (y : Domain (d := d)) : c • (0+normalizedMass p b y)=mass (MatrixGlobalHaar.child p b) y := by
    change c • (0+c⁻¹ • mass (MatrixGlobalHaar.child p b) y)=_
    rw [zero_add, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  simpa only [he] using hh

end SHEStochastic.MatrixActualColumnCalculus
