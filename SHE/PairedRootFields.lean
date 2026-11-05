module

public import SHE.PairedRootVaryingMoments
public import SHE.GaussianFibreBorel
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.PairedRootVaryingMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance GaussianDependentScores MeasurableGaussianScores
  StoppedFourier GaussianCoordinates
open scoped BigOperators
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
local instance pairedRootFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance pairedRootFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω] {n r m:ℕ}

/-- Genuine Borel dependence of the normalized paired ROOT Gaussian
average on random original past inputs, changing-rank covariances and
arbitrarily dependent current endpoint means. -/
theorem fibreAverage_measurable (P:CanonicalCovariance.ProfileParameters) (Λ θ q:ℝ)
    (u d0:Ω→CircleL2) (hu:Measurable u) (hd:Measurable d0)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (newMean oldMean:Ω→State n) (hn:Measurable newMean) (ho:Measurable oldMean)
    (leafMean:Fin m→Ω→State n) (hl:∀j,Measurable (leafMean j)) (η:Fin m→ℝ)
    (D:Ω→Fin r→State n) (hD:∀j,Measurable (fun ω=>D ω j))
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (choices:List (Fin r×Fin (m+1)))
    (F:State 1→ℝ) (hF:Measurable F) (ν χ:ℝ) :
    Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ q σ target center lo hi
      (newMean ω) (oldMean ω) (fun j=>leafMean j ω) η (D ω) g leaf choices F ν χ) := by
  let A:=fun ω=>familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi
  let B:=fun ω=>ControlledFixedReserve.covariance P Λ (u ω) (d0 ω)
    (fixedProfile P Λ (u ω) (d0 ω) lo hi) σ target center q θ
  have hA(j:Fin r):Measurable (fun ω=>A ω j):=
    VaryingControlledGaussianFields.old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j
  have hB:Measurable B:=VaryingControlledGaussianFields.residual_covariance_measurable P Λ θ q u d0 hu hd σ target center lo hi
  have hs:Measurable (fun ω=>((min 1 (ν*‖projection g (newMean ω-oldMean ω)‖))^χ)) := by
    have hp:Measurable (fun ω=>projection g (newMean ω-oldMean ω)):=by fun_prop
    exact (measurable_const.min (measurable_const.mul hp.norm)).pow_const χ
  have hr:=NormalizedScalarMoment.measurable _ _
    ((ParametricAssignedMoments.root_measurable choices 0 F hF newMean hn g).sub
      (ParametricAssignedMoments.root_measurable choices 0 F hF oldMean ho g)) (hs.comp measurable_fst)
  have hbase(j:Fin m):Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (η j,(target (leaf j),center (leaf j)))) := by
    convert! (VaryingControlledGaussianFields.profile_measurable P Λ (η j) u d0 hu hd).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j))))) using 1
  have hleaf(j:Fin m):Measurable (fun z:Ω×((Fin r→State n)×State n)=>
      ControlledAssignedLeaf.leaf choices j.succ P.coefficient (leafMean j z.1) (leaf j)
        (ControlledProfile.profile P Λ (u z.1) (d0 z.1) (η j,(target (leaf j),center (leaf j)))) z.2) :=
    VaryingAssignedFields.leaf_measurable choices j.succ P.coefficient P.measurable
      (leafMean j) (hl j) (leaf j) _ (hbase j)
  have hscore(j:Fin r):Measurable (fun z:Ω×((Fin r→State n)×State n)=>secondScore (A z.1 j) (D z.1 j) (z.2.1 j)) := by
    have hy:Measurable (fun z:Ω×((Fin r→State n)×State n)=>z.2.1 j):=
      (measurable_pi_apply j).comp measurable_snd.fst
    have ht:Measurable (fun z:Ω×((Fin r→State n)×State n)=>((A z.1 j,D z.1 j),z.2.1 j)) :=
      (((hA j).comp measurable_fst).prodMk ((hD j).comp measurable_fst)).prodMk hy
    convert! (secondScore_measurable (n:=n)).comp ht using 1
  have hw:=((Finset.measurable_prod Finset.univ (fun j _=>hscore j)).mul hr).mul
    (Finset.measurable_prod Finset.univ (fun j _=>hleaf j))
  convert! GaussianFibreBorel.average_measurable A hA B hB _ hw using 1

end SHE.PairedRootVaryingMoments
