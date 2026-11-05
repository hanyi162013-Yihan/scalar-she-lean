module

public import SHE.NativeUniversalConstants

public import SHE.MixedNativeDampedScoreEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
universe u

namespace SHE.MixedNativeDampedScoreAmplitude
open Set MeasureTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped ENNReal NNReal
local instance dampedScoreAmplitude_period : Fact (0<2*π) := ⟨by positivity⟩
local instance dampedScoreAmplitude_realSigma : MeasurableSpace RealL2 := borel _
local instance dampedScoreAmplitude_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance dampedScoreAmplitude_circleSigma : MeasurableSpace CircleL2 := borel _
local instance dampedScoreAmplitude_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance dampedScoreAmplitude_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance dampedScoreAmplitude_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance dampedScoreAmplitude_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance dampedScoreAmplitude_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

def thetaMeasure : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
instance thetaMeasure_probability : IsProbabilityMeasure thetaMeasure := ⟨by simp [thetaMeasure]⟩

variable {Ω : Type u} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable {n r : ℕ}

def score (P : CanonicalCovariance.ProfileParameters) (v q : ℝ≥0)
    (target : Fin n→ℝ) (a : Fin n→UnitAddCircle) (lo hi : Fin r→ℝ)
    (z : ℝ×(Ω×UnitAddCircle)) : ℝ :=
  MixedNativeDampedScoreEnergy.value P Λ
    (fun p : ℝ×Ω=>MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v p.2)
    (fun p : ℝ×Ω=>MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v p.2)
    (fun p : ℝ×Ω=>embed (S.second q p.2-S.first q p.2)) Prod.fst
    target (fun _=>a) ((q:ℝ)-(v:ℝ)) lo hi ((z.1,z.2.1),z.2.2)

def amplitude (P : CanonicalCovariance.ProfileParameters) (v q : ℝ≥0)
    (target : Fin n→ℝ) (a : Fin n→UnitAddCircle) (lo hi : Fin r→ℝ)
    (z : Ω×UnitAddCircle) : ℝ :=
  sqrt (∫ θ,score 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v q target a lo hi (θ,z) ∂thetaMeasure)

include hIJ₀ hIJ₁ in
/-- The actual common-driver current difference controls the entire
theta-averaged damped score amplitude in true sample/output L². Both the
varying past reserve and current direction are derived from the same S. -/
theorem actual_energy_fixed (n : ℕ) (hn : 0<n) :
    let h:=NativeUniversalConstants.currentHorizon.{u} n hn
    let C:=NativeUniversalConstants.currentConstant.{u} n hn
    ∀ (P : CanonicalCovariance.ProfileParameters),0<Λ→
      ∀ (v q : ℝ≥0),q≤H→(q:ℝ)≤1→
      ∀ (B : ℝ≥0),StandardTerminalBDGPower 1 J B→
      ∀ (target : Fin n→ℝ) (a : Fin n→UnitAddCircle) (t : Fin n→ℝ),
      (∀ i,0<t i)→(∀ i,t i≤h)→
      (∀ i,target i-((q:ℝ)-(v:ℝ))=4*π^2*t i)→
      ∀ (δ : ℝ),0<δ→(∀ i,(q:ℝ)-(v:ℝ)+δ≤target i)→
      ∀ (r : ℕ) (lo hi : Fin r→ℝ),
      (∀ j k,j≠k→hi j≤lo k ∨ hi k≤lo j)→
      let F := score 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v q target a lo hi
      let Dcur := amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v q target a lo hi
      Measurable F ∧ (∀ z,0≤F z) ∧
      Integrable F (thetaMeasure.prod (μ.prod haarAddCircle)) ∧
      Measurable Dcur ∧ MemLp Dcur 2 (μ.prod haarAddCircle) ∧
      (∫ z,Dcur z^2 ∂μ.prod haarAddCircle)≤
        (C/(3*P.lower/8))*(sqrt δ)⁻¹*(∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ) :=by
  intro h C
  have hh:=NativeUniversalConstants.currentHorizon_pos.{u} n hn
  have hh1:=NativeUniversalConstants.currentHorizon_le_one.{u} n hn
  have hC:=NativeUniversalConstants.currentConstant_pos.{u} n hn
  have he:=MixedNativeDampedScoreEnergy.reserve_energy_fixed.{u} n hn (X:=ℝ×Ω)
  intro P hΛ v q hqH hq1 B hBDG target a t ht hth hage δ hδ hmin r lo hi hdisjoint F Dcur
  let U : Ω→CircleL2 := MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
  let Dir : Ω→CircleL2 := MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
  let D : Ω→CircleL2 := fun ω=>embed (S.second q ω-S.first q ω)
  have hU : Measurable U := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir : Measurable Dir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hD : Measurable D := embed.continuous.measurable.comp
    (MixedHeatedDifferenceMoments.difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q)
  have hEi := (MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ.le q hqH hq1 1 (by decide) B hBDG).1
  have hDi : Integrable (fun ω=>‖D ω‖^2) μ := by simpa only [D,embed_norm] using hEi
  have hprod := hDi.comp_snd thetaMeasure
  have henergy := he (thetaMeasure.prod μ) P Λ hΛ (fun p : ℝ×Ω=>U p.2)
    (fun p : ℝ×Ω=>Dir p.2) (fun p : ℝ×Ω=>D p.2)
    (hU.comp measurable_snd) (hDir.comp measurable_snd) (hD.comp measurable_snd) hprod
    Prod.fst measurable_fst target (fun _=>a) (fun _=>measurable_const)
    ((q:ℝ)-(v:ℝ)) t ht hth hage δ hδ hmin r lo hi hdisjoint
  let V : (ℝ×Ω)×UnitAddCircle→ℝ := MixedNativeDampedScoreEnergy.value P Λ
    (fun p : ℝ×Ω=>U p.2) (fun p : ℝ×Ω=>Dir p.2) (fun p : ℝ×Ω=>D p.2)
    Prod.fst target (fun _=>a) ((q:ℝ)-(v:ℝ)) lo hi
  have hFm : Measurable F := henergy.1.comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  have hFn (z : ℝ×(Ω×UnitAddCircle)) : 0≤F z := henergy.2.1 ((z.1,z.2.1),z.2.2)
  have hpres := (measurePreserving_prodAssoc thetaMeasure μ
    (haarAddCircle (T:=(1:ℝ)))).symm
  have hFi : Integrable F (thetaMeasure.prod (μ.prod haarAddCircle)) := by
    exact hpres.integrable_comp_of_integrable henergy.2.2.1
  have hmass : (∫ z,F z ∂thetaMeasure.prod (μ.prod haarAddCircle))≤
      (C/(3*P.lower/8))*(sqrt δ)⁻¹*(∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ) := by
    have heq := hpres.integral_comp' V
    change (∫ z,V (MeasurableEquiv.prodAssoc.symm z) ∂thetaMeasure.prod (μ.prod haarAddCircle))≤_
    rw [heq]
    have hs : (∫ p : ℝ×Ω,‖D p.2‖^2 ∂thetaMeasure.prod μ)=
        ∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ := by
      rw [integral_prod _ hprod]
      simp only [D,embed_norm,integral_const,probReal_univ,one_smul]
    exact henergy.2.2.2.trans_eq (congrArg (fun z=>(C/(3*P.lower/8))*(sqrt δ)⁻¹*z) hs)
  have hDm : Measurable Dcur :=
    Real.continuous_sqrt.measurable.comp hFm.stronglyMeasurable.integral_prod_left'.measurable
  have hsq (z : Ω×UnitAddCircle) : Dcur z^2=∫ θ,F (θ,z) ∂thetaMeasure :=
    Real.sq_sqrt (integral_nonneg (fun θ=>hFn (θ,z)))
  have hDsq : Integrable (fun z=>Dcur z^2) (μ.prod haarAddCircle) := by
    simpa only [hsq] using hFi.integral_prod_right
  refine ⟨hFm,hFn,hFi,hDm,(memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).mpr hDsq,?_⟩
  simp_rw [hsq]
  rw [←integral_prod_symm _ hFi]
  exact hmass

include hIJ₀ hIJ₁ in
theorem actual_energy (n : ℕ) (hn : 0<n) :
    ∃ h C : ℝ,0<h ∧ h≤1 ∧ 0<C ∧
      ∀ (P : CanonicalCovariance.ProfileParameters),0<Λ→
      ∀ (v q : ℝ≥0),q≤H→(q:ℝ)≤1→
      ∀ (B : ℝ≥0),StandardTerminalBDGPower 1 J B→
      ∀ (target : Fin n→ℝ) (a : Fin n→UnitAddCircle) (t : Fin n→ℝ),
      (∀ i,0<t i)→(∀ i,t i≤h)→
      (∀ i,target i-((q:ℝ)-(v:ℝ))=4*π^2*t i)→
      ∀ (δ : ℝ),0<δ→(∀ i,(q:ℝ)-(v:ℝ)+δ≤target i)→
      ∀ (r : ℕ) (lo hi : Fin r→ℝ),
      (∀ j k,j≠k→hi j≤lo k ∨ hi k≤lo j)→
      let F := score 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v q target a lo hi
      let Dcur := amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v q target a lo hi
      Measurable F ∧ (∀ z,0≤F z) ∧
      Integrable F (thetaMeasure.prod (μ.prod haarAddCircle)) ∧
      Measurable Dcur ∧ MemLp Dcur 2 (μ.prod haarAddCircle) ∧
      (∫ z,Dcur z^2 ∂μ.prod haarAddCircle)≤
        (C/(3*P.lower/8))*(sqrt δ)⁻¹*(∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ) :=by
  exact ⟨NativeUniversalConstants.currentHorizon.{u} n hn,NativeUniversalConstants.currentConstant.{u} n hn,NativeUniversalConstants.currentHorizon_pos.{u} n hn,NativeUniversalConstants.currentHorizon_le_one.{u} n hn,NativeUniversalConstants.currentConstant_pos.{u} n hn,actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ n hn⟩

end SHE.MixedNativeDampedScoreAmplitude
