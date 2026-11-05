module
public import SHE.PastNewestTotalTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.PastNewestTimeIntegral
open Set MeasureTheory Real GaussianAssignmentBlocks PhysicalAssignmentGapScale AllocatedAssignmentKernel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain HistoryProductMeasure CoveredHistoryGeometry
open scoped BigOperators
open Classical
variable {X:Type}[MeasurableSpace X]{R:ReferenceData}{n:ℕ}(L:Level R X n)

def currentConstant (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (n k:ℕ)(span fresh A0 ν:ℝ):ℝ:=
  let cs:=assignments (m:=k+1) (List.finRange k)
  ∑i:Fin cs.length,
    (scorePrefactor ell C k*sqrt (prefactor P (cs.get i) A0 n*
      span^((P.exponent/4)*(emptyCount (cs.get i):ℝ)))*
        (max 1 (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))))^((k:ℝ)/2))*
          (((k+1:ℕ):ℝ)^2/fresh)*
            ∏j:Fin k,span^(holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2)/
              (holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2)

/-- The complete old-time RMS budget has an integrable current-time
majorant. Its constant is selected before q and before any time cutoff. -/
theorem current_bound (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(hT:∀x,L.terminal x=T)
    {ell:ℝ}(hell:0<ell)(C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(x:X)(z:Fin k→StoppedFourier.HeatCircle)
    {fresh A0 ν:ℝ}(hbase:R.base<T)(hTH:T≤R.horizon)(hf:0<fresh)(hf1:fresh≤1)(hA:0≤A0)(hν:0≤ν):
    0≤currentConstant P ell C n k (T-R.base) fresh A0 ν ∧ ∀q:ℝ,R.base≤q→q<T→
      (∫t,activeTotal L P ell C k q fresh A0 ν (separated k (x,t,z))
        ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
          currentConstant P ell C n k (T-R.base) fresh A0 ν*(T-q)^(fresh-1):=by
  let cs:=assignments (m:=k+1) (List.finRange k)
  let S:=T-R.base
  let v0:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
  let d:Fin cs.length→Fin k→ℝ:=fun i j=>holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2
  let K0:=fun i:Fin cs.length=>scorePrefactor ell C k*sqrt (prefactor P (cs.get i) A0 n*
    S^((P.exponent/4)*(emptyCount (cs.get i):ℝ)))*(max 1 v0)^((k:ℝ)/2)
  let K:=∑i:Fin cs.length,K0 i*(((k+1:ℕ):ℝ)^2/fresh)*∏j,S^(d i j)/(d i j)
  change 0≤K ∧ ∀q:ℝ,R.base≤q→q<T→
    (∫t,activeTotal L P ell C k q fresh A0 ν (separated k (x,t,z))
      ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)))≤K*(T-q)^(fresh-1)
  have hS:0<S:=sub_pos.mpr hbase
  have hd(i:Fin cs.length)(j:Fin k):0<d i j:=div_pos
    (holderDegree_pos_le_one (cs.get i) (List.get_mem cs i)
      (div_pos P.exponent_pos (by norm_num)) (by linarith [P.exponent_le_one]) j).1 (by norm_num)
  have hK0(i:Fin cs.length):0≤K0 i:=mul_nonneg
    (mul_nonneg (scorePrefactor_nonneg hell C hC k) (sqrt_nonneg _))
      (rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have hK:0≤K:=Finset.sum_nonneg (fun i _=>mul_nonneg
    (mul_nonneg (hK0 i) (div_nonneg (sq_nonneg _) hf.le))
      (Finset.prod_nonneg (fun j _=>div_nonneg (rpow_nonneg hS.le _) (hd i j).le)))
  refine ⟨hK,?_⟩
  intro q hqb hqT
  have hb:=actual_total_integral_bound L P T hT hell C hC k x z hqb hqT hTH hf hf1 hA hν
  let w:=T-q
  have hw:0<w:=sub_pos.mpr hqT
  have hwS:w≤S:=sub_le_sub_left hqb T
  have hr:w^fresh=w*w^(fresh-1):=by
    calc
      _=w^(1+(fresh-1)):=by congr 1 <;> ring
      _=w^1*w^(fresh-1):=Real.rpow_add hw _ _
      _=_:=by rw [Real.rpow_one]
  have hterm(i:Fin cs.length):
      K0 i*(((k+1:ℕ):ℝ)^2/w*∏j:Fin (k+1),w^((Fin.cons fresh (d i):Fin (k+1)→ℝ) j)/((Fin.cons fresh (d i):Fin (k+1)→ℝ) j))≤
        (K0 i*(((k+1:ℕ):ℝ)^2/fresh)*∏j,S^(d i j)/(d i j))*w^(fresh-1):=by
    have hp:(∏j:Fin k,w^(d i j)/(d i j))≤∏j:Fin k,S^(d i j)/(d i j):=
      Finset.prod_le_prod₀ (fun j _=>div_nonneg (rpow_nonneg hw.le _) (hd i j).le)
        (fun j _=>div_le_div_of_nonneg_right (rpow_le_rpow hw.le hwS (hd i j).le) (hd i j).le)
    have hcoef:0≤K0 i*(((k+1:ℕ):ℝ)^2/fresh)*w^(fresh-1):=
      mul_nonneg (mul_nonneg (hK0 i) (div_nonneg (sq_nonneg _) hf.le)) (rpow_nonneg hw.le _)
    calc
      _=(K0 i*(((k+1:ℕ):ℝ)^2/fresh)*w^(fresh-1))*(∏j:Fin k,w^(d i j)/(d i j)):=by
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ]
        rw [hr]
        field_simp [hw.ne',hf.ne']
        <;> ring
      _≤(K0 i*(((k+1:ℕ):ℝ)^2/fresh)*w^(fresh-1))*(∏j:Fin k,S^(d i j)/(d i j)):=
        mul_le_mul_of_nonneg_left hp hcoef
      _=_:=by ring
  calc
    _≤∑i:Fin cs.length,K0 i*(((k+1:ℕ):ℝ)^2/w*∏j:Fin (k+1),w^((Fin.cons fresh (d i):Fin (k+1)→ℝ) j)/((Fin.cons fresh (d i):Fin (k+1)→ℝ) j)):=by
      convert! hb.2 using 1 <;> dsimp only [K0,S,v0,d,w] <;> ring
    _≤∑i:Fin cs.length,(K0 i*(((k+1:ℕ):ℝ)^2/fresh)*∏j,S^(d i j)/(d i j))*w^(fresh-1):=
      Finset.sum_le_sum (fun i _=>hterm i)
    _=K*(T-q)^(fresh-1):=by rw [←Finset.sum_mul]

end SHE.PastNewestTimeIntegral
