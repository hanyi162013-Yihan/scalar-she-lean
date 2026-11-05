module

public import SHE.InitialAssignmentEnvelope
public import SHE.PastMeanTimeFactors
public import SHE.TerminalPairedGapIntegrals

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.InitialPhysicalEnvelope
open Set MeasureTheory Real GaussianAssignmentBlocks PhysicalAssignmentGapScale
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalScoreChain
  PhysicalParentGeometry CoveredControlledLaw CoveredHistoryGeometry
open scoped BigOperators
open Classical
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} (L:Level R X 1)

theorem time_factor_bound (P:CanonicalCovariance.ProfileParameters) {ell:ℝ} (hell:0<ell)
    (C:ℕ→ℝ) (hC:∀j,0≤C j) (k:ℕ) (p:History X k) (hp:StrictHistory L k p)
    (hb:R.base=0) (hactive:R.base<(carrier L k).terminal p)
    {h χ A0 ν:ℝ} (hh:0<h) (hχ:0≤χ) (hχβ:χ<P.exponent) (hA0:0≤A0) (hν:0≤ν)
    (hinit:initialTerminal L k p≤h)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    (hd:GapSimplexFaces.simplex h (fun j=>upper L k p j-lower L k p j)) (i:Fin (k+1)):
    timeWeight L ell C k p*
      |PairedTerminalTimeFields.factor P (fun j=>lower L k p j-R.base)
        (fun j=>upper L k p j-R.base)
        (fun j=>targets L k p (leafIndex k (fun j=>j) j)-R.base) cs χ A0 ν i|≤
      InitialAssignmentEnvelope.kernel P ell C cs h χ A0 ν i (fun j=>upper L k p j-lower L k p j):=by
  let d:=fun j=>upper L k p j-lower L k p j
  let age:=fun j=>targets L k p (leafIndex k (fun j=>j) j)-R.base
  have ha:∀j,0≤age j ∧ age j≤h:=by
    have he:=PastMeanTimeFactors.relative_ages_bounds L k p hp le_rfl hactive hinit
    simpa only [age,hb,sub_zero] using he
  have hs:=scorePrefactor_nonneg hell C hC k
  refine Fin.cases ?_ (fun j0=>?_) i
  · have he:=PastMeanTimeFactors.time_factor_bound L P hell C hC k p hp le_rfl hactive hinit hA0 hν cs hc
    simp only [hb,sub_zero] at he
    have heq:PairedTerminalTimeFields.factor P (fun j=>lower L k p j-R.base)
        (fun j=>upper L k p j-R.base) age cs χ A0 ν 0=2*PastMeanTimeFactors.factor L P k p cs A0 ν:=rfl
    change timeWeight L ell C k p*|2*PastMeanTimeFactors.factor L P k p cs A0 ν|≤_
    rw [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<2)]
    have hm:=mul_le_mul_of_nonneg_left he (by norm_num:(0:ℝ)≤2)
    convert! hm using 1
    · ring
    · simp only [InitialAssignmentEnvelope.kernel,Fin.cases_zero,
        AllocatedAssignmentKernel.assignedDensity,if_pos hd,sub_self,Real.rpow_zero,one_mul]
      ring
  · have hg:(fun j=>upper L k p j-R.base-(lower L k p j-R.base))=d:=by funext j;dsimp[d];ring
    rw [PairedTerminalTimeFields.factor,Fin.cases_succ,PairedTerminalTimeFields.roughFactor_eq_gaps,hg]
    have hnon:=TerminalPairedGapIntegrals.factor_nonneg P cs j0 χ d age
      (fun j=>(hd.1 j).le) (fun j=>(ha j).1) hA0 hν
    rw [abs_of_nonneg hnon,timeWeight_eq,mul_assoc,PairedPhysicalGapScale.inverse_factor_eq P cs hc j0 χ d age (fun j=>(ha j).1) A0 ν]
    let a:=HeterogeneousAssignmentKernel.pairedDegree P.exponent χ j0
    let freq:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
    have hw:0≤HeterogeneousAssignmentKernel.weight cs freq a d:=Finset.prod_nonneg
      (fun l _=>HeterogeneousAssignmentKernel.blockWeight_nonneg cs (mul_nonneg hν (sqrt_nonneg _)) d hd.1 l)
    have hemp:=HeterogeneousAssignmentKernel.emptyGain_bound cs a
      (fun j=>(HeterogeneousAssignmentKernel.pairedDegree_pos_le_one P.exponent_pos P.exponent_le_one hχ hχβ j0 j.succ).1.le)
      hh age ha
    have hcoef:0≤scorePrefactor ell C k*PairedPhysicalGapScale.prefactor P cs j0 χ A0*
        HeterogeneousAssignmentKernel.weight cs freq a d:=
      mul_nonneg (mul_nonneg hs (PairedPhysicalGapScale.prefactor_nonneg P cs j0 χ hA0)) hw
    have he:=mul_le_mul_of_nonneg_left hemp hcoef
    convert! he using 1
    · dsimp only [d,a,freq];ring
    · simp only [InitialAssignmentEnvelope.kernel,Fin.cases_succ,
        HeterogeneousAssignmentKernel.assignedDensity,if_pos hd,sub_self,Real.rpow_zero,one_mul]
      dsimp only [d,a,freq];ring

end SHE.InitialPhysicalEnvelope
