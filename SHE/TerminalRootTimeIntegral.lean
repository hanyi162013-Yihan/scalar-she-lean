module

public import SHE.PastMeanTimeIntegral
public import SHE.PairedTerminalTimeFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.TerminalRootTimeIntegral
open Set MeasureTheory Real GaussianAssignmentBlocks AllocatedAssignmentKernel
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays
  PhysicalParentGeometry PhysicalScoreChain CoveredControlledLaw CoveredHistoryGeometry HistoryProductMeasure
  PhysicalAssignmentGapScale
open scoped BigOperators
open Classical
variable {X:Type} [MeasurableSpace X] {R:ReferenceData}

/-- The paired ROOT slot has the FULL native rough age gain. Its old
root clips remain explicit and the original old-time measure is used. -/
theorem root_integral (L:Level R X 1) (P:CanonicalCovariance.ProfileParameters)
    (T:ℝ) (hT:∀x,L.terminal x=T) (hTH:T≤R.horizon) (hbase:R.base<T)
    {ell:ℝ} (hell:0<ell) (C:ℕ→ℝ) (hC:∀j,0≤C j)
    (k:ℕ) (x:X) (sites:Fin k→StoppedFourier.HeatCircle)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    {χ A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν):
    let W:=fun t:Fin k→ℝ=>
      let h:=separated k (x,t,sites)
      if StrictHistory L k h ∧ R.base<(carrier L k).terminal h then
        timeWeight L ell C k h*
          |PairedTerminalTimeFields.factor P (fun j=>lower L k h j-R.base)
            (fun j=>upper L k h j-R.base)
            (fun j=>targets L k h (leafIndex k (fun i:Fin (1+k)=>i) j)-R.base)
            cs χ A0 ν 0| else 0
    Integrable W (Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫t,W t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      2*scorePrefactor ell C k*prefactor P cs A0 1*
        (((k+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc (P.exponent/4))*
        (T-R.base)^((k:ℝ)*P.exponent/4)*
        rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) (T-R.base)^(rootCount cs):=by
  intro W
  have hh:=PastMeanTimeFactors.assignment_old_time_bound L P T hT hell C hC k x sites
    (q:=R.base) (fresh:=1) le_rfl hbase hTH zero_lt_one le_rfl hA0 hν cs hc
  let G:=fun t:Fin k→ℝ=>PastMeanTimeFactors.activeFactor L P ell C k R.base 1 A0 ν cs (separated k (x,t,sites))
  have he:W=fun t=>2*G t:=by
    funext t
    by_cases hp:StrictHistory L k (separated k (x,t,sites)) ∧
        R.base<(carrier L k).terminal (separated k (x,t,sites))
    · simp only [W,G,PastMeanTimeFactors.activeFactor,if_pos hp,
        PairedTerminalTimeFields.factor,Fin.cases_zero,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
        sub_self,Real.rpow_zero,one_mul,PastMeanTimeFactors.factor]
      ring
    · simp only [W,G,PastMeanTimeFactors.activeFactor,if_neg hp,mul_zero]
  refine ⟨by rw [he];exact hh.1.const_mul _,?_⟩
  rw [he,integral_const_mul]
  have hb:=mul_le_mul_of_nonneg_left hh.2 (by norm_num : (0:ℝ)≤2)
  apply hb.trans_eq
  have hw:0<T-R.base:=sub_pos.mpr hbase
  have hdeg:(P.exponent/4)*(emptyCount cs:ℝ)+
      (1+(P.exponent/4)*(roughCount cs:ℝ)-1)=(k:ℝ)*P.exponent/4:=by
    have hc':(emptyCount cs:ℝ)+(roughCount cs:ℝ)=(k:ℝ):=by exact_mod_cast empty_rough_count cs
    calc
      _=(P.exponent/4)*((emptyCount cs:ℝ)+(roughCount cs:ℝ)):=by ring
      _=_:=by rw [hc'];ring
  rw [div_one]
  calc
    _=(2*scorePrefactor ell C k*prefactor P cs A0 1*
        (((k+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc (P.exponent/4)))*
      ((T-R.base)^((P.exponent/4)*(emptyCount cs:ℝ))*
        (T-R.base)^(1+(P.exponent/4)*(roughCount cs:ℝ)-1))*
        rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) (T-R.base)^(rootCount cs):=by ring
    _=_:=by rw [←Real.rpow_add hw,hdeg]

end SHE.TerminalRootTimeIntegral
