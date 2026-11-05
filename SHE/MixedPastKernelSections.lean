module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelFields
public import SHE.PastMeanEnvelope

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

namespace SHE.MixedPastKernelSections
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastKernelSections_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastKernelSections_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastKernelSections_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastKernelSections_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastKernelSections_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastKernelSections_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastKernelSections_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastKernelSections_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastKernelSections_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

open NormalizedKernelSplit QuarterSpatialEvent
local notation "Moment" => MixedPastKernelFields.timeMoment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Genuine measurable root/time/input exchange for the literal
random-reference family. The output is AE old time followed by AE JOINT
native input/output, with one deterministic time amplitude. -/
theorem relative_moment_sections (k : ℕ) (θ : ℝ) (q : ℝ≥0) (A0 ν C : ℝ) (N : ℕ)
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspatial : ∀ᵐ x : HeatCircle ∂haarAddCircle,
      ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
        let p0:=separated k (x,t,fun _=>(0:HeatCircle))
        ∀ hp : StrictHistory Zero k p0,(q:ℝ)<(carrier Zero k).terminal p0 →
          ∀ᵐ y : HeatCircle ∂haarAddCircle,
            let r:=HistoryQuarterFields.rowTime Zero k (q:ℝ) p0
            (∫ ω,‖weightedSpatial (Base (θ,(U ω,Dir ω))) k Λ q r
              (fun _ : Unit=>Mean k θ q ω) t () y x‖^N ∂μ)≤
              C*(PastMeanAmplitude.damped Zero P k Λ q A0 ν p0*
                ScalarMeanEnvelope.massBudget Zero k p0 1 r y)^N) :
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      active Zero (b:ℝ) k q t →
        ∀ᵐ z : Space ∂(haarAddCircle (T:=2*Real.pi)).prod haarAddCircle,
          Moment k θ q N (t,z)≤C*(PastMeanEnvelope.envelope Zero P (b:ℝ) k Λ q A0 ν (t,z))^N := by
  let E : HeatCircle×((Fin k→ℝ)×HeatCircle)→Prop:=fun z=>
    active Zero (b:ℝ) k q z.2.1 → Moment k θ q N (z.2.1,(z.2.2,z.1))≤
      C*(PastMeanEnvelope.envelope Zero P (b:ℝ) k Λ q A0 ν (z.2.1,(z.2.2,z.1)))^N
  have hm:=MixedPastKernelFields.timeMoment_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q N
  have hb:=((PastMeanEnvelope.envelope_measurable Zero P (b:ℝ) k Λ q A0 ν).pow_const N).const_mul C
  have hact:MeasurableSet {z : (Fin k→ℝ)×Space | active Zero (b:ℝ) k q z.1}:=
    (active_measurableSet Zero (b:ℝ) k q).preimage measurable_fst
  have hbasic : MeasurableSet {z : (Fin k→ℝ)×Space | active Zero (b:ℝ) k q z.1 →
      Moment k θ q N z≤C*(PastMeanEnvelope.envelope Zero P (b:ℝ) k Λ q A0 ν z)^N} := by
    convert hact.compl.union (measurableSet_le hm hb) using 1
    ext z
    simp only [mem_ofPred_eq,mem_compl_iff,mem_union,imp_iff_not_or]
  have hE : MeasurableSet {z | E z}:=hbasic.preimage
    (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
  have hAE : ∀ᵐ x : HeatCircle ∂haarAddCircle,
      ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
        ∀ᵐ y : HeatCircle ∂haarAddCircle,E (x,t,y) := by
    filter_upwards [hspatial] with x hx
    filter_upwards [hx] with t ht
    by_cases ha : active Zero (b:ℝ) k q t
    · let p0:=separated k (x,t,fun _=>(0:HeatCircle))
      have hstrict : StrictHistory Zero k p0:=
        (FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) (fun _=>rfl) k t x 0 (fun _=>0) (fun _=>0)).mpr ha.1
      have hq : (q:ℝ)<(carrier Zero k).terminal p0 := by
        simpa only [p0,terminal_separated Zero (b:ℝ) (fun _=>rfl)] using ha.2
      have hrow : HistoryQuarterFields.rowTime Zero k (q:ℝ) p0=
          quarterRowTime (R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k q t :=
        HistoryQuarterFields.rowTime_separated Zero (b:ℝ) (fun _=>rfl) k q t x (fun _=>0)
      dsimp only [p0] at hrow
      filter_upwards [ht hstrict hq] with y hy
      intro _
      have heq:=PastMeanEnvelope.mass_eq_envelope Zero P (b:ℝ) (fun _=>rfl) hrootTarget hcenter
        k Λ q A0 ν t x y ha.2
      have hh:=hy
      dsimp only at hh heq
      rw [heq] at hh
      simpa only [MixedPastKernelFields.timeMoment,MixedPastKernelFields.quarterField,
        MixedPastKernelFields.timeField,MixedPastKernelFields.spatial,hrow] using hh
    · exact ae_of_all _ (fun _ h=>False.elim (ha h))
  have hs:=ae_parameter_swap (haarAddCircle (T:=2*Real.pi))
    (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))) haarAddCircle E hE hAE
  filter_upwards [hs] with t ht
  intro ha
  have hEt : MeasurableSet {z : HeatCircle×HeatCircle | E (z.1,t,z.2)} :=
    hE.preimage (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hj:=(Measure.ae_prod_iff_ae_ae hEt).mpr ht
  have hswap : MeasurePreserving (Prod.swap : Space→Space)
      ((haarAddCircle (T:=2*Real.pi)).prod haarAddCircle)
      ((haarAddCircle (T:=2*Real.pi)).prod haarAddCircle):=Measure.measurePreserving_swap
  filter_upwards [hswap.quasiMeasurePreserving.ae hj] with z hz
  exact hz ha

include hIJ₀ hIJ₁ in
/-- Actual random-past relative moments on honest joint sections. All
Gaussian, point, parent-forest, density-Jensen and Borel/Fubini premises
are discharged for the literal same/mixed joint solution. -/
theorem normalized_quarter_moment (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (θ : ℝ) (hθ : |θ|≤1) (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order : ℕ) (horder : 0<order) (B0 : ℝ≥0)
    (hBDG : StandardTerminalBDGPower (order*(k+2)) J B0)
    (q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) :
    let C:=MixedPastWordMoments.momentConstant P k k order
      ((k:ℝ)*(NativeHybridMoments.momentConstant (order*(k+2)) B0 κ M)^P.exponent)
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      active Zero (b:ℝ) k q t →
        ∀ᵐ z : Space ∂(haarAddCircle (T:=2*Real.pi)).prod haarAddCircle,
          Moment k θ q (2*order) (t,z)≤C*(PastMeanEnvelope.envelope Zero P (b:ℝ) k Λ q A0 ν (t,z))^(2*order) := by
  intro C
  have hh:=MixedPastSpatialMoments.quarter_spatial_even_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop
    (fun x i=>(hrootTarget x i).le) hspan haarAddCircle k hfresh hold θ hθ A0 ν hA0 hν hjet
    order horder B0 hBDG q hvq hqH
  exact relative_moment_sections 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    k θ q A0 ν C (2*order) hrootTarget hcenter (hh.mono (fun x hx=>hx.mono (fun t ht=>fun hp hq=>
      (ht hp hq).mono (fun y hy=>hy.2))))

end SHE.MixedPastKernelSections
