module
public import SHE.TwoFreshGaussianFields
public import SHE.TwoFreshCompleteWord
public import SHE.VaryingControlledGaussianFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
namespace SHE.TwoFreshThetaWordFields
open MeasureTheory ProbabilityTheory GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedFourier StoppedGaussianFeatures
open scoped BigOperators
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {n d r m:ℕ}

/-- The literal complete mean/covariance packet is Borel along theta,
including all original full-profile baselines and all three Gaussian laws. -/
theorem value_measurable (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d0:CircleL2)
    (q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (mean:ℝ→State n) (hm:Measurable mean) (second:Bool) (D:Fin r→State n)
    (E V:State n) (g:Fin d→Fin n) (leaf:Fin m→Fin n) (F:State d→ℝ) (hF:Measurable F):
    Measurable (fun θ=>TwoFreshCompleteWord.value P Λ u d0 θ q σ target center lo hi
      (mean θ) second D E V g leaf F):=by
  let A:=familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
  let R:=NativeFirstScoreReserve.covariance P σ target center q
  let C:=fun θ=>ControlledFixedReserve.covariance P Λ u d0
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ
  have hold:=NativeFirstScoreReserve.oldProfile_measurable P (fixedProfile_measurable P Λ u d0 lo hi)
  have hC:Measurable C:=by
    convert! StoppedGaussianFields.covariance_measurable
      (VaryingControlledGaussianFields.family (Ω:=ℝ) σ target center)
      ((ControlledProfile.profile_measurable P Λ u d0).sub (hold.comp measurable_snd))
      (measurable_const (a:=q)) using 1
  have hbase(j:Fin m):Measurable (fun θ=>ControlledProfile.profile P Λ u d0
      (θ,(target (leaf j),center (leaf j)))):=
    (ControlledProfile.profile_measurable P Λ u d0).comp (measurable_id.prodMk measurable_const)
  let cs:=assignments (m:=m+1) (List.finRange r)
  have heq:(fun θ=>TwoFreshCompleteWord.value P Λ u d0 θ q σ target center lo hi
      (mean θ) second D E V g leaf F)=fun θ=>(1/2:ℝ)^r*∑i:Fin cs.length,
        TwoFreshFullResidualMoments.fibreAverage P Λ u d0 θ q σ target center lo hi
          (mean θ) second D E V g leaf (cs.get i) F:=
    funext (fun _=>congrArg (fun a:ℝ=>(1/2:ℝ)^r*a) (FiniteAssignmentMoments.map_sum_eq_fin cs _))
  rw [heq]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact TwoFreshGaussianFields.word_average_measurable
    (fun _=>A) (fun _=>measurable_const) (fun _=>D) (fun _=>measurable_const)
    (fun _=>R) C measurable_const hC (fun _=>E) (fun _=>V) measurable_const measurable_const
    second (cs.get i) P.coefficient P.measurable F hF mean hm g leaf _ hbase

end SHE.TwoFreshThetaWordFields
