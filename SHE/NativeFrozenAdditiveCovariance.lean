module
public import SHE.NativeFrozenGaussianBlocks
public import SHE.NativeTwoPointCovariance
public import SHE.StoppedWindowCovariance
public import SHE.ObservationTimeShift
public import SHE.NonlinearTwoChannelStep
public import SHE.GaussianSeparatedCoordinates
public import SHE.GaussianRowGramCurve

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeFrozenAdditiveCovariance
open Set MeasureTheory Filter GaussianMatrixGramCurve GaussianRowGramCurve
open NativeFrozenGaussianRows GaussianContinuity ControlledProfile GaussianCovariancePath
open OrthogonalItoChannels FiniteHaar StoppedFourier
open scoped NNReal ENNReal Matrix.Norms.Elementwise
local instance unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeSigma:MeasurableSpace CircleL2:=borel _
local instance nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance bothSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance bothBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ]
variable (v b:ℝ≥0) (hvb:v≤b) (P:CanonicalCovariance.ProfileParameters) (Λ κ:ℝ) (hκ:0<κ) (hκP:κ<P.lower)
variable{n:ℕ}(side:Fin n→Bool) (ξ:Fin n→ℝ) (center:Fin n→HeatCircle)
local notation "r" p=>NativeFrozenGaussianRows.raw v b P Λ κ hκ hκP side ξ center p


local notation "C" p=>NativeFrozenGaussianCurve.curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p


local notation "Z" f=>fun i:Fin 2=>(⟨(b:ℝ),(b:ℝ),center (f i)⟩:WordRecursion.Observation)

theorem gram_entry (p:Inputs) (i j:Fin n) (hi:side i=false) (hj:side j=false)
    {t:ℝ}(ht0:0≤t)(htb:t<(b:ℝ)):
    inner ℝ ((r p) i t) ((r p) j t)=
      WordRecursion.covarianceDensity (fun _=>κ)
        (fun a:Fin n=>(⟨(b:ℝ),(b:ℝ),center a⟩:WordRecursion.Observation)) t i j:=by
  have he:=NativeObservationCovariance.row_cross_covariance hκ (AdditiveHaarForcing.constantField κ hκ)
    (fun a:Fin n=>(⟨(b:ℝ),(b:ℝ),center a⟩:WordRecursion.Observation)) t i j htb htb
  have hc:WordRecursion.covarianceDensity
      (fun q=>(CircleNormalization.push (AdditiveHaarForcing.constantField κ hκ).1 q.2).re)
      (fun a:Fin n=>(⟨(b:ℝ),(b:ℝ),center a⟩:WordRecursion.Observation)) t i j=
      WordRecursion.covarianceDensity (fun _=>κ)
      (fun a:Fin n=>(⟨(b:ℝ),(b:ℝ),center a⟩:WordRecursion.Observation)) t i j:=by
    unfold WordRecursion.covarianceDensity
    apply integral_congr_ae
    filter_upwards [NonlinearTwoChannelStep.constant_native_ae κ hκ] with x hx
    rw [hx]
  simp only [NativeFrozenGaussianRows.raw,hi,hj,Bool.false_eq_true,ite_false,
    DeterministicNativeHeatRows.raw,Real.coe_toNNReal _ ht0,ite_eq_left htb,
    NativeFrozenGaussianRows.lift,LinearIsometry.inner_map_map]
  exact he.trans hc

/-- The additive coordinate submatrix is the literal native two-point
stopped covariance at the elapsed duration. No rescaled or independent
replacement covariance is introduced. -/
theorem covariance (p:Inputs) (f:Fin 2→Fin n) (hf:∀i,side (f i)=false):
    ((C p).path (v:ℝ)).val.submatrix f f=
      NativeTwoPointCovariance.matrix ((b:ℝ)-(v:ℝ)) κ (center (f 0)) (center (f 1)):=by
  have habs:((C p).path (v:ℝ)).val.submatrix f f=
      WordRecursion.covariance (fun _=>κ) (Z f) (v:ℝ) (b:ℝ):=by
    ext i j
    rw [Matrix.submatrix_apply,NativeFrozenGaussianBlocks.covariance_entry]
    unfold WordRecursion.covariance
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (b:ℝ)] with t hne ht
    rw [uIoc_of_le (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb)] at ht
    exact gram_entry v b P Λ κ hκ hκP side ξ center p (f i) (f j) (hf i) (hf j)
      (v.2.trans ht.1.le) (lt_of_le_of_ne ht.2 hne)
  rw [habs]
  have he:=PhysicalIntervalCovariance.interval_eq_covariance (Z f) (fun _=>κ) measurable_const
    (fun _=>le_rfl:∀_q:ControlledProfile.Domain,|κ|≤|κ|) (fun _=>le_rfl) (fun _=>le_rfl)
    v.2 (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb)
  have hs:=StoppedWindowCovariance.interval_eq_clipped (Z f) (fun _=>κ) (hi:=(b:ℝ)) v.2
  change PhysicalScoreChain.intervalCovariance (Z f) (fun _=>κ) (v:ℝ) (b:ℝ)=WordRecursion.covariance (fun _=>κ) (Z f) (v:ℝ) (b:ℝ) at he
  have hshift:=ObservationTimeShift.stoppedCovariance_translation (v:ℝ) 0
    (fun _:Fin 2=>(b:ℝ)-(v:ℝ)) (fun _:Fin 2=>(b:ℝ)-(v:ℝ))
    (fun i=>center (f i)) (fun _=>κ)
  simp only [sub_add_cancel,zero_add,ObservationTimeShift.profile] at hshift
  have hfin:StoppedGaussianFeatures.stoppedCovariance (fun _:Fin 2=>(b:ℝ)-(v:ℝ))
      (fun _:Fin 2=>(b:ℝ)-(v:ℝ)) (fun i=>center (f i)) (fun _=>κ) 0=
      NativeTwoPointCovariance.matrix ((b:ℝ)-(v:ℝ)) κ (center (f 0)) (center (f 1)):=by
    unfold NativeTwoPointCovariance.matrix
    congr 1
    funext i
    fin_cases i <;> rfl
  have hst:=hshift.trans hfin
  have hst' : StoppedGaussianFeatures.stoppedCovariance
      (fun i:Fin 2=>min ((Z f) i).stop (b:ℝ)) (fun i=>((Z f) i).target)
      (fun i=>((Z f) i).center) (fun _=>κ) (v:ℝ)=
      NativeTwoPointCovariance.matrix ((b:ℝ)-(v:ℝ)) κ (center (f 0)) (center (f 1)):=by
    have hp:ObservationTimeShift.profile (v:ℝ) (fun _:ControlledProfile.Domain=>κ)=(fun _=>κ):=by
      funext z
      rfl
    rw [hp] at hst
    simpa only [min_self] using hst
  exact he.symm.trans (hs.trans hst')

end SHE.NativeFrozenAdditiveCovariance
