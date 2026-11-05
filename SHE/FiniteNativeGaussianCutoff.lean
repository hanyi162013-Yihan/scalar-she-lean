module
public import SHE.NativeGaussianWindowCutoff
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.FiniteNativeGaussianCutoff
open scoped NNReal
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
  (H:ℝ≥0)(hH:0<H)
/-- One structural cutoff for every positive depth through the fixed finite order.
It is selected before the smoothing index and damping parameter. -/
def index(N:ℕ):ℕ:=Finset.univ.sup (fun k:Fin N=>
  NativeGaussianWindowCutoff.index D hT hT1 hsmall H hH (k+1))

theorem le_index(N:ℕ)(k:Fin N):
    NativeGaussianWindowCutoff.index D hT hT1 hsmall H hH (k+1)≤
      index D hT hT1 hsmall H hH N:=by
  unfold index
  exact Finset.le_sup (f:=fun l:Fin N=>NativeGaussianWindowCutoff.index D hT hT1 hsmall H hH (l+1)) (Finset.mem_univ k)

theorem ready(N:ℕ)(J:ℕ)(hJ:index D hT hT1 hsmall H hH N≤J)(k:Fin N)(j:ℕ):
    NativeGaussianWindowCutoff.Ready D hT hT1 hsmall H (k+1) (J+j+1):=by
  apply NativeGaussianWindowCutoff.ready D hT hT1 hsmall H hH
  exact (le_index D hT hT1 hsmall H hH N k).trans (hJ.trans (by omega))
theorem le_index_of_pos(N k:ℕ)(hk:0<k)(hkN:k≤N):
    NativeGaussianWindowCutoff.index D hT hT1 hsmall H hH k≤
      index D hT hT1 hsmall H hH N:=by
  have he:k-1+1=k:=by omega
  simpa only [he] using le_index D hT hT1 hsmall H hH N ⟨k-1,by omega⟩
end SHE.FiniteNativeGaussianCutoff
