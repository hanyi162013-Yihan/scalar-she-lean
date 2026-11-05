module

public import SHE.PairedPhysicalGapIntegral
public import SHE.PairedTerminalTimeFields
public import SHE.PhysicalAssignmentTimeFactors

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.TerminalPairedGapIntegrals
open Set MeasureTheory Real GaussianAssignmentBlocks HeterogeneousAssignmentKernel
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays
  PhysicalParentGeometry PhysicalScoreChain CoveredControlledLaw CoveredHistoryGeometry HistoryProductMeasure
  OrderedGapCoordinates PhysicalOrderedGaps PhysicalAssignmentGapScale
open scoped BigOperators
open Classical
variable {X:Type} [MeasurableSpace X] {R:ReferenceData}

/-- Positivity uses the actual original root clips and all native ages,
so the terminal absolute amplitude introduces no new gap power. -/
theorem factor_nonneg {k:ℕ} (P:CanonicalCovariance.ProfileParameters)
    (cs:List (Fin k×Fin (k+1))) (j0:Fin k) (χ:ℝ) (d age:Fin k→ℝ)
    (hd:∀j,0≤d j) (ha:∀j,0≤age j) {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν):
    0≤PairedPhysicalGapScale.factor P cs j0 χ d age A0 ν:=by
  rw [PairedPhysicalGapScale.factor_eq P cs j0 χ d age ha]
  apply mul_nonneg
  · apply mul_nonneg (PairedPhysicalGapScale.prefactor_nonneg P cs j0 χ hA0)
    unfold gain
    apply Finset.prod_nonneg
    intro l _
    unfold gainBlock
    split_ifs
    · apply Finset.prod_nonneg
      intro j _
      exact le_min zero_le_one (mul_nonneg (mul_nonneg hν (sqrt_nonneg _)) (rpow_nonneg (hd _) _))
    · exact zero_le_one
    · exact rpow_nonneg (hd _) _
  · unfold emptyGain
    apply Finset.prod_nonneg
    intro j _
    split_ifs <;> first |exact rpow_nonneg (ha _) _|exact zero_le_one

/-- Genuine original old-time integration of the paired rough amplitude.
The actual minimum-gap assignments, full empty-leaf ages and every old
root clip are mapped to the exact positive-gap simplex, with no measure
normalization or independent-gap upper bound. -/
theorem rough_integral (L:Level R X 1) (P:CanonicalCovariance.ProfileParameters)
    (T:ℝ) (hT:∀x,L.terminal x=T) (hTH:T≤R.horizon) (hbase:R.base<T)
    {ell:ℝ} (hell:0<ell) (C:ℕ→ℝ) (hC:∀j,0≤C j)
    (k:ℕ) (x:X) (sites:Fin k→StoppedFourier.HeatCircle)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    (j0:Fin k) {χ A0 ν:ℝ} (hχ:0≤χ) (hχβ:χ<P.exponent) (hA0:0≤A0) (hν:0≤ν):
    let W:=fun t:Fin k→ℝ=>
      let h:=separated k (x,t,sites)
      if StrictHistory L k h ∧ R.base<(carrier L k).terminal h then
        timeWeight L ell C k h*
          |PairedTerminalTimeFields.factor P (fun j=>lower L k h j-R.base)
            (fun j=>upper L k h j-R.base)
            (fun j=>targets L k h (leafIndex k (fun i:Fin (1+k)=>i) j)-R.base)
            cs χ A0 ν j0.succ| else 0
    Integrable W (Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫t,W t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      scorePrefactor ell C k*PairedPhysicalGapScale.prefactor P cs j0 χ A0*
        (((k+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc (pairedDegree P.exponent χ j0))*
        (T-R.base)^((k:ℝ)*P.exponent/4-χ/4)*
        rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) (T-R.base)^
          (AllocatedAssignmentKernel.rootCount cs):=by
  intro W
  let age:=fun d:Fin k→ℝ=>fun j=>times T k d j-R.base
  have hage:∀d,GapSimplexFaces.simplex (T-R.base) d→∀j,0≤age d j ∧ age d j≤T-R.base:=by
    intro d hd
    have ho:ordered R.base T k (times T k d):=(ordered_iff R.base T k _).mpr (by
      rw [gaps_times]
      simpa only [GapSimplexFaces.simplex,GapSimplexReflection.slack,sub_pos] using hd)
    intro j
    have hb:=(ordered_bounds R.base T k _ ho).1 j
    exact ⟨sub_nonneg.mpr hb.1.le,sub_le_sub_right hb.2.le _⟩
  have hm(j:Fin k):Measurable (fun d=>age d j):=
    ((measurable_pi_apply j).comp (times_measurable T k)).sub_const _
  have hh:=PairedPhysicalGapScale.physical_scale_integral P cs hc j0 hχ hχβ (sub_pos.mpr hbase)
    hA0 hν age hm hage
  let F:=fun d:Fin k→ℝ=>(∏j,(d j)⁻¹)*PairedPhysicalGapScale.factor P cs j0 χ d (age d) A0 ν
  let G:=fun t:Fin k→ℝ=>if StrictHistory L k (separated k (x,t,sites)) ∧
    R.base<(carrier L k).terminal (separated k (x,t,sites)) then F (gaps T k t) else 0
  have hGi:Integrable G (Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))):=
    (active_gap_integrable_iff L T hT R.base le_rfl hTH k x sites F).mpr (by
      simpa only [GapSimplexFaces.simplex,GapSimplexReflection.slack,sub_pos] using hh.1)
  have he:W=fun t=>scorePrefactor ell C k*G t:=by
    funext t
    by_cases hp:StrictHistory L k (separated k (x,t,sites)) ∧
        R.base<(carrier L k).terminal (separated k (x,t,sites))
    · simp only [W,G,if_pos hp]
      have hg:=old_gaps_eq L T hT k t x sites hp.1
      have hl:=lower_eq_times L k t x sites hp.1
      have ht:(fun j=>targets L k (separated k (x,t,sites)) (leafIndex k (fun i:Fin (1+k)=>i) j)-R.base)=
          age (gaps T k t):=by
        funext j
        unfold targets
        rw [leaf_observation]
        change lower L k (separated k (x,t,sites)) j-R.base=_
        rw [hl]
        simp only [age,times_gaps]
      have hd:∀j,0≤gaps T k t j:=fun j=>((ordered_iff R.base T k t).mp
        ((strict_active_iff_ordered L T hT R.base le_rfl k t x sites).mp hp)).1 j |>.le
      have hs:GapSimplexFaces.simplex (T-R.base) (gaps T k t):=by
        simpa only [GapSimplexFaces.simplex,GapSimplexReflection.slack,sub_pos] using
          ((ordered_iff R.base T k t).mp
            ((strict_active_iff_ordered L T hT R.base le_rfl k t x sites).mp hp))
      have ha:=fun j=>(hage (gaps T k t) hs j).1
      simp only [PairedTerminalTimeFields.factor,Fin.cases_succ]
      rw [PairedTerminalTimeFields.roughFactor_eq_gaps]
      have hgap:(fun j=>upper L k (separated k (x,t,sites)) j-R.base-
          (lower L k (separated k (x,t,sites)) j-R.base))=gaps T k t:=by
        convert! hg using 1 <;> funext j <;> ring
      rw [hgap,ht,abs_of_nonneg (factor_nonneg P cs j0 χ _ _ hd ha hA0 hν),timeWeight_eq]
      simp_rw [congrFun hg]
      unfold F
      ring
    · simp only [W,G,if_neg hp,mul_zero]
  refine ⟨by rw [he];exact hGi.const_mul _,?_⟩
  rw [he,integral_const_mul,active_gap_integral L T hT R.base le_rfl hTH]
  have hb:=mul_le_mul_of_nonneg_left hh.2 (scorePrefactor_nonneg hell C hC k)
  convert! hb using 1
  · simp only [F,GapSimplexFaces.simplex,GapSimplexReflection.slack,sub_pos]
  · ring

end SHE.TerminalPairedGapIntegrals
