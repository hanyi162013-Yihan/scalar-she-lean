module

public import SHE.NativeMultiplierHilbertColumns
public import SHE.HilbertColumnMap
public import SHE.HilbertTrace
public import SHE.OrthogonalItoChannels

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.NativeFourierNoiseRows
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier OrthogonalItoChannels
open scoped ENNReal InnerProductSpace
local instance nativeFourierNoiseRows_period : Fact (0<2*π):=⟨by positivity⟩
abbrev Columns:=HilbertColumns.Space FiniteHaar.HaarNode CircleL2
abbrev Row:=HilbertColumns.Space FiniteHaar.HaarNode ℝ

def coefficient (l : ℤ) : CircleL2→L[ℝ]ℂ:=
  (innerSL ℂ (fourierBasis (T:=2*π) l)).restrictScalars ℝ

def realRow (l : ℤ) : Columns→L[ℝ]Row:=
  HilbertColumns.mapCLM (Complex.reCLM.comp (coefficient l))
def imagRow (l : ℤ) : Columns→L[ℝ]Row:=
  HilbertColumns.mapCLM (Complex.imCLM.comp (coefficient l))

theorem row_energy (l : ℤ) (K : Columns) :
    ‖realRow l K‖^2+‖imagRow l K‖^2=
      ∑' q : FiniteHaar.HaarNode,‖coefficient l (K q)‖^2 := by
  rw [HilbertColumns.norm_sq,HilbertColumns.norm_sq,
    ←(HilbertColumns.summable_sq (realRow l K)).tsum_add (HilbertColumns.summable_sq (imagRow l K))]
  apply tsum_congr
  intro q
  change ‖(coefficient l (K q)).re‖^2+‖(coefficient l (K q)).im‖^2=‖coefficient l (K q)‖^2
  rw [Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,sq_abs,Complex.sq_norm,Complex.normSq_apply]
  ring

/-- Genuine native Fourier Parseval for the actual infinite stochastic
columns. Both real and imaginary scalar noise rows are retained. -/
theorem trace (K : Columns) :
    Summable (fun l : ℤ=>‖realRow l K‖^2+‖imagRow l K‖^2) ∧
      (∑' l : ℤ,(‖realRow l K‖^2+‖imagRow l K‖^2))=‖K‖^2 := by
  let F:=fun p : FiniteHaar.HaarNode×ℤ=>‖coefficient p.2 (K p.1)‖^2
  have he (q : FiniteHaar.HaarNode) :
      Summable (fun l : ℤ=>F (q,l)) ∧ (∑' l : ℤ,F (q,l))=‖K q‖^2:=
    HilbertTrace.basis_sq (fourierBasis (T:=2*π)) (K q)
  have hsF : Summable (fun q : FiniteHaar.HaarNode=>∑' l : ℤ,F (q,l)):=
    (HilbertColumns.summable_sq K).congr (fun q=>(he q).2.symm)
  have hF : Summable F:=(summable_prod_of_nonneg (fun p=>sq_nonneg _)).mpr
    ⟨fun q=>(he q).1,hsF⟩
  have hsum : Summable (fun l : ℤ=>‖realRow l K‖^2+‖imagRow l K‖^2):=by
    have hh:=hF.prod_symm.prod
    change Summable (fun l : ℤ=>∑' q : FiniteHaar.HaarNode,F (q,l)) at hh
    exact hh.congr (fun l=>(row_energy l K).symm)
  refine ⟨hsum,?_⟩
  calc
    _=∑' l : ℤ,∑' q : FiniteHaar.HaarNode,F (q,l):=by simp only [row_energy,F]
    _=∑' p : ℤ×FiniteHaar.HaarNode,F (p.2,p.1):=hF.prod_symm.tsum_prod.symm
    _=∑' p : FiniteHaar.HaarNode×ℤ,F p:=(Equiv.prodComm ℤ FiniteHaar.HaarNode).tsum_eq _
    _=∑' q : FiniteHaar.HaarNode,∑' l : ℤ,F (q,l):=hF.tsum_prod
    _=∑' q : FiniteHaar.HaarNode,‖K q‖^2:=tsum_congr (fun q=>(he q).2)
    _=‖K‖^2:=(HilbertColumns.norm_sq K).symm

def bothReal (l : ℤ) (K0 K1 : Columns) : Both Row:=WithLp.toLp 2 (realRow l K0,realRow l K1)
def bothImag (l : ℤ) (K0 K1 : Columns) : Both Row:=WithLp.toLp 2 (imagRow l K0,imagRow l K1)

/-- This is exactly the original two-channel scalar input space. Its
countable Fourier row energy equals the sum of the actual column
energies, before the original scalar Itô isometry is applied. -/
theorem both_trace (K0 K1 : Columns) :
    Summable (fun l : ℤ=>‖bothReal l K0 K1‖^2+‖bothImag l K0 K1‖^2) ∧
      (∑' l : ℤ,(‖bothReal l K0 K1‖^2+‖bothImag l K0 K1‖^2))=‖K0‖^2+‖K1‖^2 := by
  have he (l : ℤ) : ‖bothReal l K0 K1‖^2+‖bothImag l K0 K1‖^2=
      (‖realRow l K0‖^2+‖imagRow l K0‖^2)+(‖realRow l K1‖^2+‖imagRow l K1‖^2) := by
    rw [bothReal,bothImag,WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
    change ‖realRow l K0‖^2+‖realRow l K1‖^2+(‖imagRow l K0‖^2+‖imagRow l K1‖^2)=_
    ring
  refine ⟨by simpa only [he] using (trace K0).1.add (trace K1).1,?_⟩
  simp only [he,((trace K0).1.tsum_add (trace K1).1),(trace K0).2,(trace K1).2]

end SHE.NativeFourierNoiseRows
