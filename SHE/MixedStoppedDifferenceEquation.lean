module

public import SHE.NativeStoppedEnergyZero
public import SHE.CountableStoppedPathAgreement
public import SHE.MixedStoppingClockCover
public import SHE.NativeVolterraAlgebra
public import SHE.MixedStoppingDifference
public import SHE.NativeFirstDampedEquation
public import SHE.NativeStoppedCoefficientInput
public import SHE.NativeStoppedNoiseIncrement
public import SHE.NativeBieleckiItoEnergy
public import SHE.AdaptedRateLocalization
public import SHE.MixedGirsanovVectorMild
public import SHE.TimeMeasureRestriction
public import SHE.HilbertItoNaturality
public import SHE.NativeGirsanovTwoChannelTransport
public import SHE.NativeDampedHaarInput
public import SHE.NativeControlMass
public import SHE.NativeHeatColumnAction
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass
public import SHE.MixedMovingEnergy
public import SHE.MixedAdditiveControl
public import SHE.CappedStochasticExponential

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedStoppedDifferenceEquation
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance (ell M:ℝ):MeasurableSpace (EllipticField ell M):=borel _
local instance (ell M:ℝ):BorelSpace (EllipticField ell M):=⟨rfl⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)


local notation "Raw"=>MixedCappedControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Cap"=>PredictableEnergyCap.capped Raw


local notation "F0"=>fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ
local notation "F1"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "Drift"=>MixedCappedDampedHeatControl.drift
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S


local instance : SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology



variable(Q:Measure Ω)[IsProbabilityMeasure Q]
variable(A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 Q H)
variable(hΛ:0≤Λ)(hH:(H:ℝ)≤1)
def additiveValue(q:ℝ≥0)(hq:q≤H):Ω→RealL2:=
  fun ω=>(A0.integral (NativeFirstDampedMild.additive 𝓕 Q H Λ κ hκ hΛ hH q hq)) ω

def residualValue(q:ℝ≥0)(hq:q≤H):Ω→RealL2:=
  fun ω=>(A1.integral (MixedGirsanovDampedMild.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Q hΛ hH q hq)) ω

variable(hV:∀(q:ℝ≥0)(hq:q≤H),∀ᵐω∂Q,PredictableEnergyCap.accumulated
  (MixedCappedControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) q ω<1→
  S.second q ω=Real.exp (-Λ*(q:ℝ)) • NativeHeatObservation.heat (q:ℝ) u₀+
    Λ • NativeClock.volterra Λ (fun s=>S.second s ω) q+
    additiveValue 𝓕 H Λ κ hκ Q A0 hΛ hH q hq ω+
    residualValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Q A1 hΛ hH q hq ω)
variable(W:NativeMildFirst.Data 𝓕 Q H κ hκ haV hell hbV A0 A1 u₀)
variable(K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 Q H)
variable(hA0:StandardScalarNaturality A0 (leftIntegral 𝓕 Q H K))
variable(hA1:StandardScalarNaturality A1 (rightIntegral 𝓕 Q H K))
variable(hlocal:StandardTerminalPastLocality A1)
variable(hpos:0<H)
variable(hcoef:Measurable (NonlinearHaarIntegrand.coefficientField aV haV ell M hell hbV))
variable(N:ℕ)(d:Process (E:=RealL2) 𝓕 Q H)
local notation "A"=>MixedStoppingClock.clock 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value N
local notation "D"=>MixedStoppingDifference.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value N
local notation "Mpos"=>hell.le.trans ((hbV 0).1.trans (hbV 0).2)
local notation "Pplus"=>NativeStoppedCoefficientInput.plus (𝓕:=𝓕) (μ:=Q) (H:=H)
  (ha:=haV) (hell:=hell) (hb:=hbV) (U:=W.value) (d:=d)
local notation "hplus"=>NativeStoppedCoefficientInput.plus_predictable (𝓕:=𝓕) (μ:=Q) (H:=H)
  (ha:=haV) (hell:=hell) (hb:=hbV) (hcoef:=hcoef) (U:=W.value) (hU:=W.predictable) (d:=d)
local notation "PW"=>ContinuousHeatMild.coefficientFunction haV hell hbV W.value

def noise(q:ℝ≥0)(ω:Ω):RealL2:=
  NativeStoppedNoiseIncrement.noise 𝓕 Q H hH hΛ hell Mpos A1 haV hbV hcoef
    (Function.uncurry W.value) W.predictable d q ω
local notation "B"=>noise (𝓕:=𝓕) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haV:=haV) (hell:=hell) (hbV:=hbV)
  (u₀:=u₀) (Q:=Q) (A0:=A0) (A1:=A1) (W:=W) (hΛ:=hΛ) (hH:=hH) (hcoef:=hcoef) (d:=d)

theorem volterra_eq(q:ℝ≥0)(ω:Ω)(hc:A q ω<1):
    NativeClock.volterra Λ (fun s=>D (s,ω)) q=
      NativeClock.volterra Λ (fun s=>S.second s ω) q-
      NativeClock.volterra Λ (fun s=>W.value s ω) q:=by
  have hm:=MixedStoppingClockProperties.monotone 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.continuous N ω
  have he(s:ℝ≥0)(hs:s≤q):D (s,ω)=S.second s ω-W.value s ω:=by
    unfold MixedStoppingDifference.value
    exact if_pos ((hm hs).trans_lt hc)
  calc
    _=NativeClock.volterra Λ (fun s=>S.second s ω-W.value s ω) q:=by
      unfold NativeClock.volterra
      apply intervalIntegral.integral_congr
      intro r hr
      have hr':r∈Icc (0:ℝ) (q:ℝ):=by
        have heq:uIcc (0:ℝ) (q:ℝ)=Icc (0:ℝ) (q:ℝ):=Set.uIcc_of_le q.2
        exact heq ▸ hr
      have hrq:r.toNNReal≤q:=by
        exact_mod_cast (show (r.toNNReal:ℝ)≤q by rw [Real.coe_toNNReal _ hr'.1];exact hr'.2)
      change Real.exp (-Λ*((q:ℝ)-r)) • NativeHeatObservation.heat ((q:ℝ)-r) (D (r.toNNReal,ω))=_
      exact congrArg (fun v:RealL2=>Real.exp (-Λ*((q:ℝ)-r)) • NativeHeatObservation.heat ((q:ℝ)-r) v) (he r.toNNReal hrq)
    _=_:=NativeVolterraAlgebra.sub Λ _ _ (S.second_continuous ω) (W.continuous ω) q

variable(hd:∀ᵐ(p:ℝ≥0×Ω)∂energyMeasure Q H,d p=
  if MixedStoppingClock.clock 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value N p.1 p.2<1
    then S.second p.1 p.2-W.value p.1 p.2 else 0)

include hA0 hA1 hlocal hd hV hpos in
theorem equation(q:ℝ≥0)(hq:q≤H):∀ᵐω∂Q,A q ω<1→
    S.second q ω-W.value q ω=Λ • NativeClock.volterra Λ (fun s=>D (s,ω)) q+B q ω:=by
  have hAa:=MixedStoppingClockProperties.adapted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.predictable W.continuous N
  have hAc:=MixedStoppingClockProperties.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.continuous N
  have hAm:=MixedStoppingClockProperties.monotone 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.continuous N
  have hrep:=NativeStoppedCoefficientInput.integral_equal (𝓕:=𝓕) (μ:=Q) (H:=H)
    (hΛ:=hΛ) (hell:=hell) (hM:=Mpos) (ha:=haV) (hb:=hbV) (hcoef:=hcoef)
    (U:=W.value) (V:=S.second) (hU:=W.predictable) (hV:=S.second_coefficient) (d:=d)
    A1 hlocal A hAa hAc hAm hpos hd q hq ((show (q:ℝ)≤H by exact_mod_cast hq).trans hH)
  have hWm:=NativeFirstDampedEquation.equation 𝓕 Q H Λ κ hκ haV hell hbV A0 A1 u₀ W K hA0 hA1 hΛ hH q hq
  have hp:=NativeBieleckiItoEnergy.value_of_le 𝓕 Q H hH hΛ hell Mpos A1 Pplus hplus q hq
  have hw:=NativeBieleckiItoEnergy.value_of_le 𝓕 Q H hH hΛ hell Mpos A1 PW W.coefficient q hq
  filter_upwards [hV q hq,hWm,hrep] with ω hv hwm hr hc
  have hraw:=MixedStoppingClockProperties.raw_le 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.continuous N q ω
  have hv:=hv (hraw.trans_lt hc)
  have hr:=hr hc
  change A1.integral (MixedGirsanovDampedMild.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Q hΛ hH q hq) ω=_ at hr
  dsimp only [additiveValue,residualValue] at hv
  rw [hr] at hv
  have hn:B q ω=
      A1.integral (NativeDampedHaarInput.input 𝓕 Q H hΛ hell Mpos Pplus hplus q hq
        ((show (q:ℝ)≤H by exact_mod_cast hq).trans hH)) ω-
      A1.integral (NativeDampedHaarInput.input 𝓕 Q H hΛ hell Mpos PW W.coefficient q hq
        ((show (q:ℝ)≤H by exact_mod_cast hq).trans hH)) ω:=by
    unfold noise NativeStoppedNoiseIncrement.noise
    change NativeBieleckiItoEnergy.value 𝓕 Q H hH hΛ hell Mpos A1 Pplus hplus q ω-
      NativeBieleckiItoEnergy.value 𝓕 Q H hH hΛ hell Mpos A1 PW W.coefficient q ω=_
    rw [hp,hw]
  dsimp only [NativeFirstDampedMild.residual] at hwm
  have he:S.second q ω-W.value q ω=
      Λ • (NativeClock.volterra Λ (fun s=>S.second s ω) q-
        NativeClock.volterra Λ (fun s=>W.value s ω) q)+B q ω:=by
    rw [hn,hv,hwm]
    module
  rw [←volterra_eq (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁)
    (u₀:=u₀) (S:=S) (Q:=Q) (A0:=A0) (A1:=A1) (W:=W) (N:=N) q ω hc] at he
  exact he
include hA0 hA1 hlocal hd hV hpos in
theorem norm_bound(q:ℝ≥0)(hq:q≤H):∀ᵐω∂Q,
    ‖D (q,ω)‖^2≤2*Λ^2*‖NativeClock.volterra Λ (fun s=>D (s,ω)) q‖^2+2*‖B q ω‖^2:=by
  have he:=equation (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁)
    (u₀:=u₀) (S:=S) (Q:=Q) (A0:=A0) (A1:=A1) (hΛ:=hΛ) (hH:=hH) (hV:=hV)
    (W:=W) (K:=K) (hA0:=hA0) (hA1:=hA1) (hlocal:=hlocal) (hpos:=hpos)
    (hcoef:=hcoef) (N:=N) (d:=d) (hd:=hd) q hq
  filter_upwards [he] with ω he
  by_cases hc:A q ω<1
  · have hdq:D (q,ω)=S.second q ω-W.value q ω:=by
      unfold MixedStoppingDifference.value
      exact if_pos hc
    rw [hdq,he hc]
    have hn:=norm_add_le (Λ • NativeClock.volterra Λ (fun s=>D (s,ω)) q) (B q ω)
    rw [norm_smul,Real.norm_of_nonneg hΛ] at hn
    nlinarith only [hn,norm_nonneg (Λ • NativeClock.volterra Λ (fun s=>D (s,ω)) q+B q ω),
      norm_nonneg (NativeClock.volterra Λ (fun s=>D (s,ω)) q),norm_nonneg (B q ω),
      sq_nonneg (Λ*‖NativeClock.volterra Λ (fun s=>D (s,ω)) q‖-‖B q ω‖)]
  · have hdq:D (q,ω)=0:=by
      unfold MixedStoppingDifference.value
      exact if_neg hc
    rw [hdq,norm_zero,zero_pow (by decide:2≠0)]
    positivity

include hA0 hA1 hlocal hd hV hpos hcoef in
theorem eq_zero{L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(aV z:ℂ))):d=0:=by
  have hDm:=MixedStoppingDifference.predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.predictable W.continuous N
  have hrep : (fun p=>D p)=ᵐ[energyMeasure Q H] d:=by
    filter_upwards [hd] with p hp
    exact hp.symm
  apply NativeStoppedEnergyZero.eq_zero 𝓕 Q H hH hΛ hell Mpos A1 haV hbV hcoef hLip
    (Function.uncurry W.value) W.predictable d (fun q ω=>D (q,ω))
    (hDm.mono (predictable_le_product 𝓕)).measurable hrep
  · exact MixedStoppingDifference.path_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.predictable W.continuous N
  · filter_upwards [timeMeasure_ae_mem H] with q hq
    exact norm_bound (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁)
      (u₀:=u₀) (S:=S) (Q:=Q) (A0:=A0) (A1:=A1) (hΛ:=hΛ) (hH:=hH) (hV:=hV)
      (W:=W) (K:=K) (hA0:=hA0) (hA1:=hA1) (hlocal:=hlocal) (hpos:=hpos)
      (hcoef:=hcoef) (N:=N) (d:=d) (hd:=hd) q hq.2

include hA0 hA1 hlocal hV hpos hcoef in
/-- The actual controlled companion and the canonical smooth solution
agree for their whole native paths on the raw no-exit event. The proof
constructs countably many genuine stopped inputs and proves each zero. -/
theorem path_agreement{L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(aV z:ℂ))):
    ∀ᵐω∂Q,PredictableEnergyCap.accumulated Raw H ω<1→
      ∀t:ℝ≥0,t≤H→S.second t ω=W.value t ω:=by
  apply CountableStoppedPathAgreement.off_exit_ae Q H hpos S.second W.value
    S.second_continuous W.continuous
    (MixedStoppingClock.clock 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value)
  · intro N ω
    exact MixedStoppingClockProperties.monotone 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.continuous N ω
  · exact ae_of_all _ (fun ω=>MixedStoppingClockCover.covers 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.continuous ω)
  · intro N
    obtain ⟨d,hd,_⟩:=MixedStoppingClock.exists_difference_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S W.value W.predictable W.continuous Q N
    have hz:=eq_zero (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁)
      (u₀:=u₀) (S:=S) (Q:=Q) (A0:=A0) (A1:=A1) (hΛ:=hΛ) (hH:=hH) (hV:=hV)
      (W:=W) (K:=K) (hA0:=hA0) (hA1:=hA1) (hlocal:=hlocal) (hpos:=hpos)
      (hcoef:=hcoef) (N:=N) (d:=d) (hd:=hd) hLip
    have hdz:∀ᵐp∂energyMeasure Q H,d p=0:=by
      rw [hz]
      exact ae_eq_of_ae_eq_trim (Lp.coeFn_zero RealL2 2 ((energyMeasure Q H).trim (predictable_le_product 𝓕)))
    filter_upwards [hd,hdz] with p hp hp0
    exact hp.symm.trans hp0

end SHE.MixedStoppedDifferenceEquation
