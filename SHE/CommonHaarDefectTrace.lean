module

public import SHE.FiniteCovariancePullback
public import SHE.JointNativeDefect

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.CommonHaarDefectTrace
open MeasureTheory GaussianIncrement GaussianTaylorAverage FiniteHaar
open scoped BigOperators

def direction {n:ℕ}(R:Fin n→RealHaarInput)(j:HaarNode):State n:=
  WithLp.toLp 2 (fun i=>R i j)

/-- Exact contraction against the SAME countable Haar coordinates.
This identity keeps the sign of every mixed Hessian entry. -/
theorem cross_trace {n:ℕ}(R S:Fin n→RealHaarInput)
    (B:State n→L[ℝ]State n→L[ℝ]ℝ):
    Summable (fun j:HaarNode=>B (direction R j) (direction S j)) ∧
    (∑'j:HaarNode,B (direction R j) (direction S j))=
      covarianceAction (fun i k=>inner ℝ (R i) (S k)) B:=by
  let e:=EuclideanSpace.basisFun (Fin n) ℝ
  let F:=fun j:HaarNode=>fun i k:Fin n=>R i j*S k j*B (e i) (e k)
  have hs(i k:Fin n):Summable (fun j:HaarNode=>F j i k):=by
    have hh:Summable (fun j:HaarNode=>R i j*S k j):=by
      simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using lp.summable_inner (𝕜:=ℝ) (R i) (S k)
    exact hh.mul_right _
  have hb(j:HaarNode):B (direction R j) (direction S j)=∑i:Fin n,∑k:Fin n,F j i k:=
    FiniteCovariancePullback.bilinear_basis B _ _
  have hsum:Summable (fun j:HaarNode=>∑i:Fin n,∑k:Fin n,F j i k):=
    summable_sum (fun i _=>summable_sum (fun k _=>hs i k))
  refine ⟨hsum.congr (fun j=>(hb j).symm),?_⟩
  simp_rw [hb]
  rw [Summable.tsum_finsetSum (fun i _=>summable_sum (fun k _=>hs i k))]
  simp_rw [Summable.tsum_finsetSum (fun k _=>hs _ k)]
  unfold covarianceAction
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [show (∑'j:HaarNode,F j i k)=(∑'j:HaarNode,R i j*S k j)*B (e i) (e k) from tsum_mul_right]
  congr 1
  change (∑'j:HaarNode,R i j*S k j)=inner ℝ (R i) (S k)
  simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using
    (lp.inner_eq_tsum (𝕜:=ℝ) (f:=R i) (g:=S k)).symm

/-- Both cross terms AND the quadratic term of the direct joint defect
are contracted against the true Haar coordinates, without polarization
or discarding any contribution. -/
theorem full_trace {n:ℕ}(U V:Fin n→RealHaarInput)(r:Fin n→ℝ)
    (B:State n→L[ℝ]State n→L[ℝ]ℝ):
    let D:=fun i=>r i • (U i-V i)
    Summable (fun j:HaarNode=>B (direction D j) (direction V j)+
      B (direction V j) (direction D j)+B (direction D j) (direction D j)) ∧
    covarianceAction (fun i k=>r i*inner ℝ (U i-V i) (V k)+
      r k*inner ℝ (V i) (U k-V k)+r i*r k*inner ℝ (U i-V i) (U k-V k)) B=
      (∑'j:HaarNode,(B (direction D j) (direction V j)+
        B (direction V j) (direction D j)+B (direction D j) (direction D j))):=by
  intro D
  obtain ⟨hs1,he1⟩:=cross_trace D V B
  obtain ⟨hs2,he2⟩:=cross_trace V D B
  obtain ⟨hs3,he3⟩:=cross_trace D D B
  refine ⟨(hs1.add hs2).add hs3,?_⟩
  rw [Summable.tsum_add (hs1.add hs2) hs3,Summable.tsum_add hs1 hs2,he1,he2,he3]
  unfold covarianceAction
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [D,real_inner_smul_left,real_inner_smul_right]
  ring

end SHE.CommonHaarDefectTrace
