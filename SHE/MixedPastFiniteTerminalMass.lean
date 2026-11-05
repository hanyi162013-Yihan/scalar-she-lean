module

public import SHE.MixedPastEndpointScoreEnergy
public import SHE.TerminalSuccessorGeometry
public import SHE.BoundedResidualFields

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastFiniteTerminalMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastCovarianceSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- True finite-profile future score mass on original relative old-space
coordinates at the actual newest terminal time. -/
def scoreMass (k:ℕ) (ζ:ℝ) (t:Fin (k+1)→ℝ)
    (z:(Ω×HeatCircle)×(Fin (k+1)→HeatCircle)):ℝ:=
  let a:=anchor (k+1) t
  let σ:=fun i=>stops Zero (k+1) a i-(v:ℝ)
  let target:=fun i=>targets Zero (k+1) a i-(v:ℝ)
  let lo:=fun j=>lower Zero (k+1) a j-(v:ℝ)
  let hi:=fun j=>upper Zero (k+1) a j-(v:ℝ)
  let c:=BoundedWindowDecomposition.residual P Λ (U z.1.1) (Dir z.1.1) lo hi
    (BoundedWindowDecomposition.convexProfile P Λ (U z.1.1) (Dir z.1.1) 1 0 (1-ζ))
  let e:=fun p=>ControlledProfile.profile P Λ (U z.1.1) (Dir z.1.1) (1,p)-
    ControlledProfile.profile P Λ (U z.1.1) (Dir z.1.1) (0,p)
  futureInput σ target (values (fun _:Fin 1=>(0:HeatCircle)) (k+1) z.2) c e
    ((carrier Zero (k+1)).terminal a-(v:ℝ)) z.1.2

local notation "Mass"=>scoreMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Joint Borel mass before old-space, output or sample sections. -/
theorem scoreMass_measurable (k:ℕ) (ζ:ℝ) (t:Fin (k+1)→ℝ):Measurable (Mass k ζ t):=by
  let a:=anchor (k+1) t
  let σ:=fun i=>stops Zero (k+1) a i-(v:ℝ)
  let target:=fun i=>targets Zero (k+1) a i-(v:ℝ)
  let lo:=fun j=>lower Zero (k+1) a j-(v:ℝ)
  let hi:=fun j=>upper Zero (k+1) a j-(v:ℝ)
  let u:Ω×(Fin (k+1)→HeatCircle)→CircleL2:=fun z=>U z.1
  let d:Ω×(Fin (k+1)→HeatCircle)→CircleL2:=fun z=>Dir z.1
  have hU:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hD:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hu:Measurable u:=hU.comp measurable_fst
  have hd:Measurable d:=hD.comp measurable_fst
  let c:(Ω×(Fin (k+1)→HeatCircle))×ControlledProfile.Domain→ℝ:=fun z=>
    BoundedWindowDecomposition.residual P Λ (u z.1) (d z.1) lo hi
      (BoundedWindowDecomposition.convexProfile P Λ (u z.1) (d z.1) 1 0 (1-ζ)) z.2
  let e:(Ω×(Fin (k+1)→HeatCircle))×ControlledProfile.Domain→ℝ:=fun z=>
    ControlledProfile.profile P Λ (u z.1) (d z.1) (1,z.2)-ControlledProfile.profile P Λ (u z.1) (d z.1) (0,z.2)
  have hc:Measurable c:=(BoundedResidualFields.convexProfile_measurable P Λ 1 0 (1-ζ) u d hu hd).sub
    (VaryingControlledGaussianFields.fixed_profile_measurable P Λ u d hu hd lo hi)
  have he:Measurable e:=(VaryingControlledGaussianFields.profile_measurable P Λ 1 u d hu hd).sub
    (VaryingControlledGaussianFields.profile_measurable P Λ 0 u d hu hd)
  let center:Ω×(Fin (k+1)→HeatCircle)→Fin (1+(k+1))→HeatCircle:=fun z=>
    values (fun _:Fin 1=>(0:HeatCircle)) (k+1) z.2
  have hcenter:Measurable center:=(values_continuous (fun _:Fin 1=>(0:HeatCircle)) (k+1)).measurable.comp measurable_snd
  have hh:=futureInput_random_centers_measurable σ target center hcenter c e hc he
    ((carrier Zero (k+1)).terminal a-(v:ℝ))
  have hmap:Measurable (fun z:(Ω×HeatCircle)×(Fin (k+1)→HeatCircle)=>((z.1.1,z.2),z.1.2)):=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  convert! hh.comp hmap using 1

include hIJ₀ hIJ₁ in
/-- Sharp actual endpoint mass in the ORIGINAL root/old-space frame.
The zero-newest-future-age coordinate is removed exactly; the bound has
true past energy to beta and NO negative earliest-gap loss. -/
theorem actual_mass_energy (hΛ:0≤Λ)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H) (hv1:(v:ℝ)≤1) (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (k:ℕ) (t:Fin (k+1)→ℝ)
    (hp:StrictHistory Zero (k+1) (anchor (k+1) t)) {ζ:ℝ} (hζ:0≤ζ) (hζ1:ζ≤1):
    ∀w:Fin (k+1)→HeatCircle,
      let C:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
      Integrable (fun z:Ω×HeatCircle=>|Mass k ζ t (z,w)|^2) (μ.prod haarAddCircle) ∧
        (∫z:Ω×HeatCircle,|Mass k ζ t (z,w)|^2 ∂μ.prod haarAddCircle)≤
          C^2*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)^P.exponent:=by
  intro w C
  let a:=anchor (k+1) t
  let σ:=fun i=>stops Zero k a.1 i-(v:ℝ)
  let target:=fun i=>targets Zero k a.1 i-(v:ℝ)
  let lo:=fun j=>lower Zero (k+1) a j-(v:ℝ)
  let hi:=fun j=>upper Zero (k+1) a j-(v:ℝ)
  let q:ℝ:=(carrier Zero k).nodeTime a-(v:ℝ)
  have hq:0≤q:=sub_nonneg.mpr ((carrier Zero k).nodeTime_mem a).1
  have hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j:=RelativeHistoryGeometry.relative_disjoint Zero (k+1) a
  have hs1(i):σ i-q≤1:=by
    have hs:σ i≤1:=(RelativeHistoryGeometry.relative_stop_le_span Zero (b:ℝ) (fun _=>le_rfl) k a.1 i).trans
      (hspan.trans P.horizon_le_one)
    linarith
  have hage(i):σ i≤target i:=sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k a.1 i)) _
  have hnode:(carrier Zero k).nodeTime a=a.2.1:=ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
  have hqstop:q<(carrier Zero k).terminal a.1-(v:ℝ):=by
    dsimp only [q]
    rw [hnode]
    exact sub_lt_sub_right hp.2.2 _
  have hstops(i):(carrier Zero k).terminal a.1-(v:ℝ)≤σ i:=sub_le_sub_right
    (le_min ((carrier Zero k).stops_after a.1 i) (terminal_le_initial Zero k a.1)) _
  have hs:(fun i=>stops Zero (k+1) a i-(v:ℝ))=Fin.cons q σ:=by
    rw [TerminalSuccessorGeometry.stops_succ]
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  have ht:(fun i=>targets Zero (k+1) a i-(v:ℝ))=Fin.cons q target:=by
    rw [TerminalSuccessorGeometry.targets_succ]
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  have hh:=MixedPastEndpointScoreEnergy.actual_endpoint_mass_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ v P hΛ hsmallL2 hvH hv1 Bpast hBDGpast
    q hq 1 0 (w 0) (ζ:=1-ζ) (by linarith) (by linarith) lo hi hdisjoint (1+k) σ target
    (values (fun _:Fin 1=>(0:HeatCircle)) k (fun i=>w i.succ)) hs1 hage
    ((carrier Zero k).terminal a.1-(v:ℝ)) hqstop hstops
  dsimp only [a] at hs ht
  have htime:(carrier Zero (k+1)).terminal (anchor (k+1) t)-(v:ℝ)=q:=rfl
  simpa only [scoreMass,hs,ht,htime,lo,hi,a,OrderedHeatForests.values,
    sub_zero,abs_one,Real.one_rpow,mul_one] using hh

end SHE.MixedPastFiniteTerminalMass
