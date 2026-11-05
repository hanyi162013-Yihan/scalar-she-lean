module

public import SHE.ObservationBlockMaps
public import SHE.AffineStateJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.AffineBlockAction
open GaussianIncrement GaussianTaylor GaussianTaylorAverage ObservationBlockMaps
variable {n : ℕ}

@[simp] theorem first_basis_first (i : Fin n) :
    first n (EuclideanSpace.basisFun (Fin (n+n)) ℝ (Fin.castAdd n i))=
      EuclideanSpace.basisFun (Fin n) ℝ i := by
  apply PiLp.ext
  intro j
  simp [first_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply]

@[simp] theorem second_basis_first (i : Fin n) :
    second n (EuclideanSpace.basisFun (Fin (n+n)) ℝ (Fin.castAdd n i))=0 := by
  apply PiLp.ext
  intro j
  have hne : Fin.natAdd n j≠Fin.castAdd n i := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
    omega
  change (EuclideanSpace.basisFun (Fin (n+n)) ℝ (Fin.castAdd n i)) (Fin.natAdd n j)=0
  rw [EuclideanSpace.basisFun_apply]
  exact PiLp.single_eq_of_ne 2 hne 1

@[simp] theorem first_basis_second (i : Fin n) :
    first n (EuclideanSpace.basisFun (Fin (n+n)) ℝ (Fin.natAdd n i))=0 := by
  apply PiLp.ext
  intro j
  have hne : Fin.castAdd n j≠Fin.natAdd n i := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
    omega
  change (EuclideanSpace.basisFun (Fin (n+n)) ℝ (Fin.natAdd n i)) (Fin.castAdd n j)=0
  rw [EuclideanSpace.basisFun_apply]
  exact PiLp.single_eq_of_ne 2 hne 1

@[simp] theorem second_basis_second (i : Fin n) :
    second n (EuclideanSpace.basisFun (Fin (n+n)) ℝ (Fin.natAdd n i))=
      EuclideanSpace.basisFun (Fin n) ℝ i := by
  apply PiLp.ext
  intro j
  simp [second_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply]

def linear (c : ℝ) : State (n+n)→L[ℝ]State n := first n+c • second n

@[simp] theorem linear_basis_first (c : ℝ) (i : Fin n) :
    linear c (EuclideanSpace.basisFun (Fin (n+n)) ℝ (Fin.castAdd n i))=
      EuclideanSpace.basisFun (Fin n) ℝ i := by
  simp only [linear,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    first_basis_first,second_basis_first,smul_zero,add_zero]

@[simp] theorem linear_basis_second (c : ℝ) (i : Fin n) :
    linear c (EuclideanSpace.basisFun (Fin (n+n)) ℝ (Fin.natAdd n i))=
      c • EuclideanSpace.basisFun (Fin n) ℝ i := by
  simp only [linear,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    first_basis_second,second_basis_second,zero_add]

/-- Literal block contraction retains both ordered mixed pairs. -/
def mixed (A : Matrix (Fin (n+n)) (Fin (n+n)) ℝ) (c : ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  A (Fin.castAdd n i) (Fin.castAdd n j)+c*A (Fin.castAdd n i) (Fin.natAdd n j)+
    c*A (Fin.natAdd n i) (Fin.castAdd n j)+c^2*A (Fin.natAdd n i) (Fin.natAdd n j)

theorem covarianceAction_affine {F : State n→ℝ} (hF : ContDiff ℝ 2 F)
    (A : Matrix (Fin (n+n)) (Fin (n+n)) ℝ) (c : ℝ) (m : State n) (z : State (n+n)) :
    covarianceAction A (hessian (fun y => F (linear c y+m)) z)=
      covarianceAction (mixed A c) (hessian F (linear c z+m)) := by
  simp only [covarianceAction,hessian]
  simp_rw [AffineStateJets.hessian_affine_apply hF]
  rw [Fin.sum_univ_add]
  simp_rw [Fin.sum_univ_add,linear_basis_first,linear_basis_second,map_smul,ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [mixed]
  ring

end SHE.AffineBlockAction
