module

public import SHE.NativeUniversalConstants

public import SHE.NativeMeanAveraging
public import SHE.NativeFirstScoreReserve
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedPastJointData
public import SHE.MixedCurrentInputMoments
public import SHE.CorrelatedCurrentHolder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
universe u

namespace SHE.MixedNativeDampedScoreEnergy
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  GaussianIncrement MeasurableGaussianScores PhysicalMeanRange NativeMeanFields StoppedGaussianScore
  ControlledOldIntervals NativeHeatObservation PredictableL2 NativeObservationNaturality
  StoppedMeanEnergy RealHeatCovarianceMean
  FiniteHaar OrthogonalItoChannels DyadicApproximation
open scoped ENNReal NNReal
local instance dampedScoreEnergy_period : Fact (0<2*π) := ⟨by positivity⟩
local instance dampedScoreEnergy_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance dampedScoreEnergy_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance dampedScoreEnergy_unitSigma : MeasurableSpace HeatTorus.CircleL2 := borel _
local instance dampedScoreEnergy_unitBorel : BorelSpace HeatTorus.CircleL2 := ⟨rfl⟩

variable {X : Type u} [MeasurableSpace X] {n r : ℕ}
attribute [local irreducible] ControlledProfile.profile

/-- The literal residual covariance after the fixed old half-profile and
the independent native first-score eighth have both been removed. -/
def value (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d D : X→CircleL2) (θ : X→ℝ) (target : Fin n→ℝ)
    (a : X→Fin n→UnitAddCircle) (q : ℝ) (lo hi : Fin r→ℝ)
    (z : X×UnitAddCircle) : ℝ :=
  scoreVariance (ControlledFixedReserve.covariance P Λ (u z.1) (d z.1)
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u z.1) (d z.1) lo hi))
    target target (nativeCenter (fun i=>a z.1 i+z.2)) q (θ z.1))
    (dampedDirection target target (fun i=>a z.1 i+z.2) q Λ (D z.1))

/-- Sharp spatial score energy for the actual varying canonical reserve.
All data may depend on the same parameter; no fixed-law substitution or
independence assumption is used. The witnesses depend only on dimension. -/
theorem reserve_energy_fixed (n : ℕ) (hn : 0<n) :
    let h:=NativeUniversalConstants.currentHorizon.{u} n hn
    let C:=NativeUniversalConstants.currentConstant.{u} n hn
    ∀ {X : Type u} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
      (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ),0<Λ→
      ∀ (u d D : X→CircleL2),Measurable u→Measurable d→Measurable D→
      Integrable (fun y=>‖D y‖^2) ν→
      ∀ (θ : X→ℝ),Measurable θ→
      ∀ (target : Fin n→ℝ) (a : X→Fin n→UnitAddCircle),
      (∀ i,Measurable (fun y=>a y i))→
      ∀ (q : ℝ) (t : Fin n→ℝ),(∀ i,0<t i)→(∀ i,t i≤h)→
      (∀ i,target i-q=4*π^2*t i)→
      ∀ (δ : ℝ),0<δ→(∀ i,q+δ≤target i)→
      ∀ (r : ℕ) (lo hi : Fin r→ℝ),
      (∀ j k,j≠k→hi j≤lo k ∨ hi k≤lo j)→
      Measurable (value P Λ u d D θ target a q lo hi) ∧
      (∀ z,0≤value P Λ u d D θ target a q lo hi z) ∧
      Integrable (value P Λ u d D θ target a q lo hi) (ν.prod haarAddCircle) ∧
      (∫ z,value P Λ u d D θ target a q lo hi z ∂ν.prod haarAddCircle)≤
        (C/(3*P.lower/8))*(sqrt δ)⁻¹*(∫ y,‖D y‖^2 ∂ν) :=by
  intro h C
  have hh:=NativeUniversalConstants.currentHorizon_pos.{u} n hn
  have hh1:=NativeUniversalConstants.currentHorizon_le_one.{u} n hn
  have hC:=NativeUniversalConstants.currentConstant_pos.{u} n hn
  intro X _ ν _ P Λ hΛ u d D hu hd hD hDi θ hθ target a ha q t ht hth hage δ hδ hmin r lo hi hdisjoint
  have he:=(NativeUniversalConstants.current_spec.{u} n hn).2.2.2 (X:=X)
  let c : (X×UnitAddCircle)×ControlledProfile.Domain→ℝ := fun z=>
    ControlledFixedReserve.coefficient P Λ (u z.1.1) (d z.1.1)
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u z.1.1) (d z.1.1) lo hi))
      (θ z.1.1) z.2
  have hmap : Measurable (fun z : X×ControlledProfile.Domain=>((z.1,θ z.1),z.2)) :=
    (measurable_fst.prodMk (hθ.comp measurable_fst)).prodMk measurable_snd
  have hprof := (ControlledProfile.random_profile_measurable P hu hd Λ).comp hmap
  have hold := VaryingControlledGaussianFields.fixed_profile_measurable P Λ u d hu hd lo hi
  have hc0 : Measurable (fun z : X×ControlledProfile.Domain=>
      ControlledFixedReserve.coefficient P Λ (u z.1) (d z.1)
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u z.1) (d z.1) lo hi)) (θ z.1) z.2) :=
    hprof.sub (hold.add_const (NativeFirstScoreReserve.floor P))
  have hcmap : Measurable (fun z : (X×UnitAddCircle)×ControlledProfile.Domain=>(z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hc : Measurable c := hc0.comp hcmap
  have hell : 0<3*P.lower/8 := by have := P.lower_pos; positivity
  have hb (p : X×UnitAddCircle) (z : ControlledProfile.Domain) :
      3*P.lower/8≤c (p,z) ∧ c (p,z)≤P.upper :=
    NativeFirstScoreReserve.residual_bounds P Λ (u p.1) (d p.1)
      (fixedProfile_bounds P Λ (u p.1) (d p.1) lo hi hdisjoint) (θ p.1) z
  let du : X→HeatTorus.CircleL2 := fun y=>CircleNormalization.push.symm (D y)
  have hdu : Measurable du := CircleNormalization.push.symm.continuous.measurable.comp hD
  have hdui : Integrable (fun y=>‖du y‖^2) ν := by simpa only [du,LinearIsometryEquiv.norm_map] using hDi
  have act : ∀ i,q<target i := fun i=>by linarith [hmin i]
  let f := meanScoreEnergy target a q Λ t hage act c du
  have hEq : f=value P Λ u d D θ target a q lo hi := by
    funext z
    dsimp only [f,meanScoreEnergy,value,ControlledFixedReserve.covariance]
    rw [←dampedDirection_eq target target (fun i=>a z.1 i+z.2) q Λ t ht hage act (D z.1)]
  have hm : Measurable f := meanScoreEnergy_measurable target a ha q Λ t ht hage act c hc du hdu
  have hnon (z : X×UnitAddCircle) : 0≤f z := meanScoreEnergy_nonneg target a q Λ hΛ t hage act
    δ hδ hmin c hc P.upper (3*P.lower/8)
    (fun p z=>⟨hell.le.trans (hb p z).1,(hb p z).2⟩) hell (fun p z=>(hb p z).1) du z
  have hi := he ν target a ha q Λ hΛ t ht hth hage δ hδ hmin c hc P.upper (3*P.lower/8)
    (fun p z=>⟨hell.le.trans (hb p z).1,(hb p z).2⟩) hell (fun p z=>(hb p z).1) du hdu hdui
  change Integrable f (ν.prod haarAddCircle) ∧
    (∫ z,f z ∂ν.prod haarAddCircle)≤(C/(3*P.lower/8))*(sqrt δ)⁻¹*(∫ y,‖du y‖^2 ∂ν) at hi
  rw [hEq] at hm hnon hi
  exact ⟨hm,hnon,hi.1,by simpa only [du,LinearIsometryEquiv.norm_map] using hi.2⟩

theorem reserve_energy (n : ℕ) (hn : 0<n) :
    ∃ h C : ℝ,0<h ∧ h≤1 ∧ 0<C ∧
      ∀ {X : Type u} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
      (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ),0<Λ→
      ∀ (u d D : X→CircleL2),Measurable u→Measurable d→Measurable D→
      Integrable (fun y=>‖D y‖^2) ν→
      ∀ (θ : X→ℝ),Measurable θ→
      ∀ (target : Fin n→ℝ) (a : X→Fin n→UnitAddCircle),
      (∀ i,Measurable (fun y=>a y i))→
      ∀ (q : ℝ) (t : Fin n→ℝ),(∀ i,0<t i)→(∀ i,t i≤h)→
      (∀ i,target i-q=4*π^2*t i)→
      ∀ (δ : ℝ),0<δ→(∀ i,q+δ≤target i)→
      ∀ (r : ℕ) (lo hi : Fin r→ℝ),
      (∀ j k,j≠k→hi j≤lo k ∨ hi k≤lo j)→
      Measurable (value P Λ u d D θ target a q lo hi) ∧
      (∀ z,0≤value P Λ u d D θ target a q lo hi z) ∧
      Integrable (value P Λ u d D θ target a q lo hi) (ν.prod haarAddCircle) ∧
      (∫ z,value P Λ u d D θ target a q lo hi z ∂ν.prod haarAddCircle)≤
        (C/(3*P.lower/8))*(sqrt δ)⁻¹*(∫ y,‖D y‖^2 ∂ν) :=by
  exact ⟨NativeUniversalConstants.currentHorizon.{u} n hn,NativeUniversalConstants.currentConstant.{u} n hn,NativeUniversalConstants.currentHorizon_pos.{u} n hn,NativeUniversalConstants.currentHorizon_le_one.{u} n hn,NativeUniversalConstants.currentConstant_pos.{u} n hn,@reserve_energy_fixed.{u} n hn⟩

end SHE.MixedNativeDampedScoreEnergy
