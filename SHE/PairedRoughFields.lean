module

public import SHE.PairedRoughVaryingMoments
public import SHE.GaussianFibreBorel
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PairedRoughVaryingMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance GaussianDependentScores MeasurableGaussianScores StoppedFourier
open scoped BigOperators
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
local instance pairedRoughFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance pairedRoughFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω] {n r m:ℕ}

/-- The literal normalized paired ROUGH Gaussian average is Borel even
when the original past data, all covariance ranks and both current
endpoint means vary together. -/
theorem fibreAverage_measurable (P:CanonicalCovariance.ProfileParameters) (Λ θ ηOld ηNew q:ℝ)
    (u d0:Ω→CircleL2) (hu:Measurable u) (hd:Measurable d0)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (newMean oldMean rootMean:Ω→State n) (hn:Measurable newMean) (ho:Measurable oldMean) (hr:Measurable rootMean)
    (choose:Fin m→Bool) (D:Ω→Fin r→State n) (hD:∀j,Measurable (fun ω=>D ω j))
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (choices:List (Fin r×Fin (m+1))) (j0:Fin m)
    (F:State 1→ℝ) (hF:Measurable F) (χ:ℝ) :
    Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ ηOld ηNew q σ target center lo hi
      (newMean ω) (oldMean ω) (rootMean ω) choose (D ω) g leaf choices j0 F χ) := by
  let A:=fun ω=>familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi
  let B:=fun ω=>ControlledFixedReserve.covariance P Λ (u ω) (d0 ω)
    (fixedProfile P Λ (u ω) (d0 ω) lo hi) σ target center q θ
  have hA(j:Fin r):Measurable (fun ω=>A ω j):=
    VaryingControlledGaussianFields.old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j
  have hB:Measurable B:=VaryingControlledGaussianFields.residual_covariance_measurable P Λ θ q u d0 hu hd σ target center lo hi
  have hbase(η:ℝ)(j:Fin m):Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (η,(target (leaf j),center (leaf j)))) := by
    convert! (VaryingControlledGaussianFields.profile_measurable P Λ η u d0 hu hd).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j))))) using 1
  have hln(j:Fin m):Measurable (fun z:Ω×((Fin r→State n)×State n)=>
      ControlledAssignedLeaf.leaf choices j.succ P.coefficient (newMean z.1) (leaf j)
        (ControlledProfile.profile P Λ (u z.1) (d0 z.1) (ηNew,(target (leaf j),center (leaf j)))) z.2) :=
    VaryingAssignedFields.leaf_measurable choices j.succ P.coefficient P.measurable newMean hn (leaf j) _ (hbase ηNew j)
  have hlo(j:Fin m):Measurable (fun z:Ω×((Fin r→State n)×State n)=>
      ControlledAssignedLeaf.leaf choices j.succ P.coefficient (oldMean z.1) (leaf j)
        (ControlledProfile.profile P Λ (u z.1) (d0 z.1) (ηOld,(target (leaf j),center (leaf j)))) z.2) :=
    VaryingAssignedFields.leaf_measurable choices j.succ P.coefficient P.measurable oldMean ho (leaf j) _ (hbase ηOld j)
  have hcoordn:Measurable (fun ω=>newMean ω (leaf j0)):=
    (EuclideanSpace.proj (𝕜:=ℝ) (leaf j0)).continuous.measurable.comp hn
  have hcoordo:Measurable (fun ω=>oldMean ω (leaf j0)):=
    (EuclideanSpace.proj (𝕜:=ℝ) (leaf j0)).continuous.measurable.comp ho
  have hs:Measurable (fun ω=>PairedRoughWordMoments.source P choices j0.succ χ
      (newMean ω) (oldMean ω) (leaf j0)
      (ControlledProfile.profile P Λ (u ω) (d0 ω) (ηNew,(target (leaf j0),center (leaf j0))))
      (ControlledProfile.profile P Λ (u ω) (d0 ω) (ηOld,(target (leaf j0),center (leaf j0))))) := by
    unfold PairedRoughWordMoments.source
    split_ifs
    · unfold NormalizedPairedLeaf.source
      exact (measurable_const.mul ((continuous_abs.measurable.comp (hcoordn.sub hcoordo)).pow_const χ)).add
        ((continuous_abs.measurable.comp ((hbase ηNew j0).sub (hbase ηOld j0))).pow_const (χ/P.exponent))
    · exact (continuous_abs.measurable.comp (hcoordn.sub hcoordo)).pow_const χ
  have hp:=NormalizedScalarMoment.measurable _ _ ((hln j0).sub (hlo j0)) (hs.comp measurable_fst)
  have hleaf(j:Fin m):Measurable (fun z:Ω×((Fin r→State n)×State n)=>
      if j=j0 then PairedRoughWordMoments.value P choices j0.succ χ (newMean z.1) (oldMean z.1) (leaf j0)
        (ControlledProfile.profile P Λ (u z.1) (d0 z.1) (ηNew,(target (leaf j0),center (leaf j0))))
        (ControlledProfile.profile P Λ (u z.1) (d0 z.1) (ηOld,(target (leaf j0),center (leaf j0)))) z.2
      else ControlledAssignedLeaf.leaf choices j.succ P.coefficient (if choose j then newMean z.1 else oldMean z.1)
        (leaf j) (ControlledProfile.profile P Λ (u z.1) (d0 z.1)
          ((if choose j then ηNew else ηOld),(target (leaf j),center (leaf j)))) z.2) := by
    by_cases hj:j=j0
    · simp only [hj,ite_true,PairedRoughWordMoments.value]
      exact hp
    · simp only [hj,ite_false]
      cases hc:choose j
      · simpa only [hc,Bool.false_eq_true,ite_false] using hlo j
      · simpa only [hc,ite_true] using hln j
  have hscore(j:Fin r):Measurable (fun z:Ω×((Fin r→State n)×State n)=>secondScore (A z.1 j) (D z.1 j) (z.2.1 j)) := by
    have hy:Measurable (fun z:Ω×((Fin r→State n)×State n)=>z.2.1 j):=
      (measurable_pi_apply j).comp measurable_snd.fst
    have ht:Measurable (fun z:Ω×((Fin r→State n)×State n)=>((A z.1 j,D z.1 j),z.2.1 j)) :=
      (((hA j).comp measurable_fst).prodMk ((hD j).comp measurable_fst)).prodMk hy
    convert! (secondScore_measurable (n:=n)).comp ht using 1
  have hw:=((Finset.measurable_prod Finset.univ (fun j _=>hscore j)).mul
    (ParametricAssignedMoments.root_measurable choices 0 F hF rootMean hr g)).mul
    (Finset.measurable_prod Finset.univ (fun j _=>hleaf j))
  convert! GaussianFibreBorel.average_measurable A hA B hB _ hw using 1

end SHE.PairedRoughVaryingMoments
