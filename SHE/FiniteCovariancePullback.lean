module

public import SHE.GaussianProjectionInsertion
public import SHE.StandardFiniteIto

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FiniteCovariancePullback
open scoped ContDiff
open GaussianIncrement GaussianTaylor GaussianTaylorAverage SmoothCylinders
variable {n m : ℕ}

def coefficient (L : State m→L[ℝ]State n) (i : Fin n) (j : Fin m) : ℝ :=
  L (EuclideanSpace.basisFun (Fin m) ℝ j) i

def mappedRow {C : Type*} [AddCommGroup C] [Module ℝ C]
    (L : State m→L[ℝ]State n) (R : Fin m→C) (i : Fin n) : C :=
  ∑ j,coefficient L i j • R j

def gram {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    (R : Fin m→C) : Matrix (Fin m) (Fin m) ℝ := fun i j=>inner ℝ (R i) (R j)

theorem hessian_comp (L : State m→L[ℝ]State n) {F : State n→ℝ}
    (hF : BoundedSmooth F) (z u v : State m) :
    hessian (fun w=>F (L w)) z u v=hessian F (L z) (L u) (L v) := by
  have h:=congrArg (fun T=>T ![u,v]) (L.iteratedFDeriv_comp_right hF.smooth z
    (by simp : (2:WithTop ℕ∞)≤∞))
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply,hessian,Function.comp_def] using h

theorem bilinear_basis (B : State n→L[ℝ]State n→L[ℝ]ℝ) (x y : State n) :
    B x y=∑ i:Fin n,∑ j:Fin n,x i*y j*B
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  let e:=EuclideanSpace.basisFun (Fin n) ℝ
  have hx : (∑ i:Fin n,x i • e i)=x:=by simpa only [e,EuclideanSpace.basisFun_repr] using e.sum_repr x
  have hy : (∑ i:Fin n,y i • e i)=y:=by simpa only [e,EuclideanSpace.basisFun_repr] using e.sum_repr y
  calc
    B x y=(B (∑ i:Fin n,x i • e i)) y := by rw [hx]
    _=∑ i:Fin n,x i*B (e i) y := by
      simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul]
    _=∑ i:Fin n,∑ j:Fin n,x i*y j*B (e i) (e j) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        x i*B (e i) y=x i*B (e i) (∑ j:Fin n,y j • e j) := by rw [hy]
        _=∑ j:Fin n,x i*y j*B (e i) (e j) := by
          simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

theorem gram_mappedRow {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    (L : State m→L[ℝ]State n) (R : Fin m→C) (i j : Fin n) :
    gram (mappedRow L R) i j=∑ a:Fin m,∑ b:Fin m,
      coefficient L i a*coefficient L j b*gram R a b := by
  unfold gram mappedRow
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro a _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [real_inner_smul_left,real_inner_smul_right]
  ring

private theorem four_sum_comm (T : Fin m→Fin m→Fin n→Fin n→ℝ) :
    (∑ a,∑ b,∑ i,∑ j,T a b i j)=∑ i,∑ j,∑ a,∑ b,T a b i j := by
  calc
    _=∑ a,∑ i,∑ b,∑ j,T a b i j := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _=∑ i,∑ a,∑ b,∑ j,T a b i j := Finset.sum_comm
    _=∑ i,∑ j,∑ a,∑ b,T a b i j := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _=∑ a,∑ j,∑ b,T a b i j := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _=∑ j,∑ a,∑ b,T a b i j := Finset.sum_comm

/-- The full finite mixed covariance sum transforms by the actual
linear observation map, without a diagonal or independence approximation. -/
theorem action_pullback {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    (L : State m→L[ℝ]State n) (R : Fin m→C)
    (B : State n→L[ℝ]State n→L[ℝ]ℝ) :
    (∑ a:Fin m,∑ b:Fin m,gram R a b*B
      (L (EuclideanSpace.basisFun (Fin m) ℝ a))
      (L (EuclideanSpace.basisFun (Fin m) ℝ b)))=
      covarianceAction (gram (mappedRow L R)) B := by
  let e:=EuclideanSpace.basisFun (Fin n) ℝ
  let f:=EuclideanSpace.basisFun (Fin m) ℝ
  let T:=fun a b i j=>gram R a b*(L (f a) i*L (f b) j*B (e i) (e j))
  have hl : (∑ a:Fin m,∑ b:Fin m,gram R a b*B (L (f a)) (L (f b)))=
      ∑ a:Fin m,∑ b:Fin m,∑ i:Fin n,∑ j:Fin n,T a b i j := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [bilinear_basis]
    simp only [Finset.mul_sum]
    rfl
  rw [hl,four_sum_comm]
  unfold covarianceAction
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gram_mappedRow,Finset.sum_mul]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp [T,coefficient,e,f]
  ring

end SHE.FiniteCovariancePullback
