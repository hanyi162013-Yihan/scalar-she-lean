module

public import SHE.NativeFirstOmittedPointwise
public import SHE.TwoFreshControlledFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.NativeFirstOmittedFields
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianDependentScores GaussianScoreKernel
  MeasurableGaussianScores StoppedFourier StoppedGaussianFeatures ControlledOldIntervals OldIntervalCovariance
open scoped BigOperators
local instance nativeFirstOmittedFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*} [MeasurableSpace Ω] {n d r m:ℕ}

/-- Joint Borel integration of an omitted leaf with a native first score.
The remaining fresh covariance is integrated without a score. -/
theorem word_average_measurable
    (A:Ω→Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,Measurable (fun ω=>A ω j))
    (D:Ω→Fin r→State n) (hD:∀j,Measurable (fun ω=>D ω j))
    (R C:Ω→MeasurableGeneralizedInverse.Mat n) (hR:Measurable R) (hC:Measurable C)
    (E:Ω→State n) (hE:Measurable E)
    (choices:List (Fin r×Fin (m+1))) (j0:Fin m) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:Ω→State n) (hm:Measurable mean)
    (g:Fin d→Fin n) (leaf:Fin m→Fin n) (baseline:Ω→Fin m→ℝ)
    (hbase:∀j,Measurable (fun ω=>baseline ω j)):
    Measurable (fun ω=>∫x,NativeFirstOmittedMoments.word (A ω) (D ω) (R ω) (E ω)
      choices j0 a F (fun _:Unit=>mean ω) g leaf (baseline ω) ((),x)
      ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A ω j))).prod
        ((multivariateGaussian (0:State n) (R ω)).prod (multivariateGaussian (0:State n) (C ω)))):=by
  have hold(j:Fin r):Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>
      secondScore (A z.1 j) (D z.1 j) (z.2.1 j)):=by
    have hy:Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>z.2.1 j):=
      (measurable_pi_apply j).comp measurable_snd.fst
    have hp:Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>((A z.1 j,D z.1 j),z.2.1 j)):=
      (((hA j).comp measurable_fst).prodMk ((hD j).comp measurable_fst)).prodMk hy
    convert! secondScore_measurable.comp hp using 1
  have hnative:Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>firstScore (R z.1) (E z.1) z.2.2.1):=by
    convert! firstScore_measurable.comp
      (((hR.comp measurable_fst).prodMk (hE.comp measurable_fst)).prodMk measurable_snd.snd.fst) using 1
  have hcp:Measurable (NativeFirstOmittedMoments.collapse (Ω:=Ω) (r:=r) (n:=n)):=by
    unfold NativeFirstOmittedMoments.collapse
    fun_prop
  have hroot:=(ParametricAssignedMoments.root_measurable choices 0 F hF mean hm g).comp hcp
  have hleaves:=Finset.measurable_prod (Finset.univ.erase j0)
    (fun j _=>(VaryingAssignedFields.leaf_measurable choices j.succ a ha mean hm (leaf j)
      (fun ω=>baseline ω j) (hbase j)).comp hcp)
  apply TwoFreshGaussianFields.average_measurable A hA R C hR hC
    (fun z=>NativeFirstOmittedMoments.word (A z.1) (D z.1) (R z.1) (E z.1)
      choices j0 a F (fun _:Unit=>mean z.1) g leaf (baseline z.1) ((),z.2))
  convert! (((Finset.measurable_prod Finset.univ (fun j _=>hold j)).mul hnative).mul hroot).mul hleaves using 1

variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- The literal controlled omitted fibre is Borel when both past states,
the current mean and every insertion direction vary together. -/
theorem fibreAverage_measurable (P:CanonicalCovariance.ProfileParameters) (Λ θ q:ℝ)
    (u d0:Ω→CircleL2) (hu:Measurable u) (hd:Measurable d0)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (mean:Ω→State n) (hm:Measurable mean)
    (D:Ω→Fin r→State n) (hD:∀j,Measurable (fun ω=>D ω j))
    (E:Ω→State n) (hE:Measurable E)
    (g:Fin d→Fin n) (leaf:Fin m→Fin n) (choices:List (Fin r×Fin (m+1))) (j0:Fin m)
    (F:State d→ℝ) (hF:Measurable F):
    Measurable (fun ω=>NativeFirstOmittedMoments.fibreAverage P Λ (u ω) (d0 ω) θ q
      σ target center lo hi (mean ω) (D ω) (E ω) g leaf choices j0 F):=by
  have hbase(j:Fin m):Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (θ,(target (leaf j),center (leaf j)))):=by
    convert! (VaryingControlledGaussianFields.profile_measurable P Λ θ u d0 hu hd).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j))))) using 1
  exact word_average_measurable _
    (fun j=>VaryingControlledGaussianFields.old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j)
    D hD _ _ measurable_const (TwoFreshControlledFields.residual_covariance_measurable P Λ θ q u d0 hu hd σ target center lo hi)
    E hE choices j0 P.coefficient P.measurable F hF mean hm g leaf _ hbase

end SHE.NativeFirstOmittedFields
