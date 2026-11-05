module
public import SHE.GaussianCoordinates
public import Mathlib.MeasureTheory.Function.L2Space
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.BrownianFiniteCovariance
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable{ι:Type*}[DecidableEq ι]{n:ℕ}

def matrix(a:Fin n→ι)(t:Fin n→ℝ≥0):Matrix (Fin n) (Fin n) ℝ:=
  fun i j=>(min (t i) (t j):ℝ≥0)*(if a i=a j then 1 else 0:ℝ)

/-- The actual finite Brownian time/coordinate covariance is positive
semidefinite, with repeated coordinates and coincident times retained. -/
theorem posSemidef(a:Fin n→ι)(t:Fin n→ℝ≥0):(matrix a t).PosSemidef:=by
  classical
  let A:=Finset.univ.image a
  letI:MeasurableSpace A:=⊤
  letI:MeasurableSingletonClass A:=⟨fun _=>trivial⟩
  let ν:Measure (A×ℝ):=Measure.count.prod volume
  let b:Fin n→A:=fun i=>⟨a i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
  let s:Fin n→Set (A×ℝ):=fun i=>{b i}×ˢIcc 0 (t i:ℝ)
  have hm(i:Fin n):MeasurableSet (s i):=(measurableSet_singleton _).prod measurableSet_Icc
  have hf(i:Fin n):ν (s i)≠∞:=by
    simp[ν,s,Measure.prod_prod]
  have he:matrix a t=Matrix.of (fun i j=>ν.real (s i∩s j)):=by
    ext i j
    by_cases h:a i=a j
    · have hb:b i=b j:=Subtype.ext h
      simp[matrix,s,ν,prod_inter_prod,hb,Icc_inter_Icc,Measure.real,Measure.prod_prod,h,ENNReal.toReal_min]
    · have hb:b i≠b j:=fun he=>h (congrArg Subtype.val he)
      simp[matrix,s,ν,prod_inter_prod,hb,Measure.real,h]
  rw[he]
  exact posSemidef_matrix_measure_inter hm hf
end SHE.BrownianFiniteCovariance
