module

public import SHE.NativeFullHaarRanges
public import SHE.ScalarDefectCovarianceGeometry
public import SHE.NativeFirstScoreReserve
public import SHE.RelativeHistoryGeometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace SHE.ControlledDefectFreshRanges
open Set MeasureTheory Real AddCircle FiniteHaar StoppedFourier StoppedGaussianScore
  StoppedGaussianFeatures GaussianIncrement MeasurableGaussianScores CommonHaarDefectTrace
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays
  PhysicalParentGeometry PhysicalScoreChain CoveredControlledLaw ControlledProfile ControlledOldIntervals
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩

/-- The two ACTUAL fresh laws of an all-order scalar history admit
every original clipped/current Haar direction. No rank or conditioning
assumption, or extra Gaussian law, is supplied. -/
theorem ranges {R:ReferenceData}(L:Level R HeatCircle 1)(T:ℝ)(hT:∀x,L.terminal x=T)
    (hroot:∀x i,(L.observations.observations x i).stop=T ∧
      (L.observations.observations x i).target=T ∧ (L.observations.observations x i).center=x)
    (P:CanonicalCovariance.ProfileParameters)(Λ:ℝ)(hΛ:0<Λ)(p:ℝ×(CircleL2×CircleL2))
    (k:ℕ)(h:History HeatCircle k)(q:ℝ)(hvq:R.base≤q)(hqt:q<(carrier L k).terminal h)
    {m W:ℝ}(hm:0<m)(f g:EllipticField m W):
    let σ:=fun i=>stops L k h i-R.base
    let target:=fun i=>targets L k h i-R.base
    let center:=centers L k h
    let a:=fun i=>(CircleNormalization.scale 1 (2*Real.pi)).symm (center i)
    let lo:=fun j=>lower L k h j-R.base
    let hi:=fun j=>upper L k h j-R.base
    let RN:=NativeFirstScoreReserve.covariance P σ target center (q-R.base)
    let RC:=ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.2.1 p.2.2 lo hi))
      σ target center (q-R.base) p.1
    let D:=NativeClippedHaarDirection.column hm f g σ target a (q-R.base) Λ
    let Wr:=direction (fun i=>NativeObservationCovariance.row hm g (target i) (q-R.base) (center i))
    (∀l,D l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) RN).range) ∧
      Summable (fun l=>scoreVariance RN (D l)) ∧
      (∀l,Wr l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) RN).range) ∧
      Summable (fun l=>scoreVariance RN (Wr l)) ∧
      (∀l,D l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) RC).range) ∧
      Summable (fun l=>scoreVariance RC (D l)) ∧
      (∀l,Wr l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) RC).range) ∧
      Summable (fun l=>scoreVariance RC (Wr l)):=by
  intro σ target center a lo hi RN RC D Wr
  have hs:σ=target:=by
    funext i
    exact congrArg (fun z:ℝ=>z-R.base)
      (congrFun (ScalarDefectCovarianceGeometry.covered_stop_eq_target L T hT hroot k h) i)
  have hgap(i:Fin (1+k)):q-R.base<target i:=by
    have hh:=(carrier L k).targets_after h i
    change (carrier L k).terminal h≤targets L k h i at hh
    dsimp only [target]
    linarith
  have ha:StoppedGaussianScore.nativeCenter a=center:=by
    funext i
    exact (CircleNormalization.scale 1 (2*Real.pi)).apply_symm_apply _
  have hold:=fixedProfile_bounds P Λ p.2.1 p.2.2 lo hi (RelativeHistoryGeometry.relative_disjoint L k h)
  let c:ControlledProfile.Domain→ℝ:=ControlledFixedReserve.coefficient P Λ p.2.1 p.2.2
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.2.1 p.2.2 lo hi)) p.1
  have hc:Measurable c:=
    (((ControlledProfile.profile_measurable P Λ p.2.1 p.2.2).comp
      (measurable_const.prodMk measurable_id))).sub
      (NativeFirstScoreReserve.oldProfile_measurable P (fixedProfile_measurable P Λ p.2.1 p.2.2 lo hi))
  have hb(z:ControlledProfile.Domain):0≤c z ∧ c z≤P.upper:=by
    have hh:=NativeFirstScoreReserve.residual_bounds P Λ p.2.1 p.2.2 hold p.1 z
    constructor
    · exact (by have :=P.lower_pos;positivity:0≤3*P.lower/8).trans hh.1
    · exact hh.2
  have hell:0<P.lower/8:=by have :=P.lower_pos;positivity
  have hcl(z:ControlledProfile.Domain):P.lower/8≤c z:=by
    have hh:=NativeFirstScoreReserve.residual_bounds P Λ p.2.1 p.2.2 hold p.1 z
    linarith [P.lower_pos]
  have hN:=NativeFullHaarRanges.ranges (by omega:0<1+k) target a (q-R.base) Λ hΛ hgap
    (fun _=>P.lower/8) measurable_const (P.lower/8) (P.lower/8)
    (fun _=>⟨hell.le,le_rfl⟩) hell (fun _=>le_rfl) hm f g
  have hC:=NativeFullHaarRanges.ranges (by omega:0<1+k) target a (q-R.base) Λ hΛ hgap
    c hc P.upper (P.lower/8) hb hell hcl hm f g
  dsimp only [RN,RC,NativeFirstScoreReserve.covariance,NativeFirstScoreReserve.floor,
    ControlledFixedReserve.covariance,D,Wr]
  rw [hs,←ha]
  exact ⟨hN.1,hN.2.1,hN.2.2.1,hN.2.2.2,hC.1,hC.2.1,hC.2.2.1,hC.2.2.2⟩

end SHE.ControlledDefectFreshRanges
