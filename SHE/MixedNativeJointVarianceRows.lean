module

public import SHE.MixedNativeJointRowFields
public import SHE.NativeRowProductEnergy
public import SHE.ScalarHeatSixNorms
public import SHE.NativeJointGammaFields
public import SHE.MixedPastReferenceInput
public import SHE.FirstGammaCanonicalReferenceEnergy
public import SHE.ScalarHeatGradientOpenTime
public import SHE.ControlledVarianceGammaTime

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeJointVarianceRows
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower)
variable (hΛ:0≤Λ) (v b:ℝ≥0) (hvb:v<b) (hbH:b≤H) (hH:(H:ℝ)≤1)
variable (hwindow:(b:ℝ)-(v:ℝ)≤P.horizon)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "OldUM"=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable)
local notation "OldDM"=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v)).measurable)
local notation "Bbound"=>((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH)


local notation "UU"=>Function.uncurry S.first
local notation "VV"=>Function.uncurry S.second

local notation "Fields"=>MixedNativeJointRowFields.fields 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH
local notation "Grad"=>MixedNativeVarianceGammaTime.gradient 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b
def currentMean (U V:ℝ≥0×Ω→RealL2) (Λ:ℝ) (v b:ℝ≥0) (p:ℝ×(Ω×HeatCircle)):ℝ:=
  NativeJointGammaFields.current (v:=v) (b:=b) (U:=U) (V:=V) (Λ:=Λ) 1
    ((((b:ℝ)-p.1).toNNReal,p.2.1),p.2.2)
local notation "Cur"=>currentMean UU VV Λ v b

local notation "Ref"=>MixedNativeVarianceGammaTime.referenceMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH

theorem current_point (a:ℝ→ℝ) (j:ℕ) (t:ℝ) (ht:t∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))) (z:Ω×HeatCircle):
    ‖Fields a j 1 ((((b:ℝ)-t).toNNReal,z.1),z.2)-
      Fields a j 2 ((((b:ℝ)-t).toNNReal,z.1),z.2)‖^2=|Grad a j Cur (t,z)|^2:=by
  change ‖((deriv (ScalarGaussianSemigroup.heat
      (NativeJointGammaFields.variance (v:=v) (b:=b) (U:=UU) (V:=VV) (P:=P) (Λ:=Λ) 0
        ((((b:ℝ)-t).toNNReal,z.1),z.2)).toNNReal (ScalarHeatBands.band a (j+1))) (Cur (t,z)):ℝ):ℂ)-
    ((deriv (ScalarGaussianSemigroup.heat
      (NativeJointGammaFields.variance (v:=v) (b:=b) (U:=UU) (V:=VV) (P:=P) (Λ:=Λ) 1
        ((((b:ℝ)-t).toNNReal,z.1),z.2)).toNNReal (ScalarHeatBands.band a (j+1))) (Cur (t,z)):ℝ):ℂ)‖^2=_
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  dsimp only [MixedNativeVarianceGammaTime.gradient]
  rw [MixedNativeJointRowFields.variance_age_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b 0 t ht z,
    MixedNativeJointRowFields.variance_age_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b 1 t ht z]

theorem reference_point (a:ℝ→ℝ) (j:ℕ) (t:ℝ) (ht:t∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))) (z:Ω×HeatCircle):
    ‖Fields a j 4 ((((b:ℝ)-t).toNNReal,z.1),z.2)-
      Fields a j 5 ((((b:ℝ)-t).toNNReal,z.1),z.2)‖^2=|Grad a j Ref (t,z)|^2:=by
  change ‖((deriv (ScalarGaussianSemigroup.heat
      (NativeJointGammaFields.variance (v:=v) (b:=b) (U:=UU) (V:=VV) (P:=P) (Λ:=Λ) 0
        ((((b:ℝ)-t).toNNReal,z.1),z.2)).toNNReal (ScalarHeatBands.band a (j+1))) (Ref (t,z)):ℝ):ℂ)-
    ((deriv (ScalarGaussianSemigroup.heat
      (NativeJointGammaFields.variance (v:=v) (b:=b) (U:=UU) (V:=VV) (P:=P) (Λ:=Λ) 1
        ((((b:ℝ)-t).toNNReal,z.1),z.2)).toNNReal (ScalarHeatBands.band a (j+1))) (Ref (t,z)):ℝ):ℂ)‖^2=_
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  dsimp only [MixedNativeVarianceGammaTime.gradient]
  rw [MixedNativeJointRowFields.variance_age_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b 0 t ht z,
    MixedNativeJointRowFields.variance_age_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b 1 t ht z]

include hvb in
/-- Exact expected native-row energy, with the original sample and spatial measures. -/
theorem current_sample {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A:ℝ} (hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (j:ℕ) (t:ℝ) (ht:t∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))):
    (∫ω,‖NativeRandomRows.nativeRow (Fields a j 1) (((b:ℝ)-t).toNNReal,ω)-
      NativeRandomRows.nativeRow (Fields a j 2) (((b:ℝ)-t).toNNReal,ω)‖^2 ∂μ)=
        ∫z,|Grad a j Cur (t,z)|^2 ∂μ.prod haarAddCircle:=by
  have hm(i:Fin 6):Measurable (Fields a j i):=
    MixedNativeJointRowFields.fields_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
      v b hvb hbH hH hnull B0 B1 hBDG0 hBDG1 a ha j i
  have hb(i:Fin 6)(p:ℝ≥0×Ω)(x:HeatCircle):‖Fields a j i (p,x)‖≤ScalarHeatSingleMultiplier.cap A P.exponent j:=
    MixedNativeJointRowFields.fields_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
      v b hbH hH ha hA hholder j i p x
  rw [(NativeRowProductEnergy.difference μ (Fields a j 1) (Fields a j 2) (hm 1) (hm 2) (hb 1) (hb 2) _).2]
  exact integral_congr_ae (ae_of_all _ (fun z=>current_point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
    v b hbH hH a j t ht z))

include hIJ₀ hIJ₁ hΛ hH hvb hbH hwindow hsmall hBDGpast in
/-- The ACTUAL current variance-change row has the sharp future-time gain.
No independent-mean or past-moment budget is assumed. -/
theorem current_energy {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (j:ℕ):
    IntegrableOn (fun t=>t^(ρ-1/2)*(∫ω,‖NativeRandomRows.nativeRow (Fields a j 1) (((b:ℝ)-t).toNNReal,ω)-
      NativeRandomRows.nativeRow (Fields a j 2) (((b:ℝ)-t).toNNReal,ω)‖^2 ∂μ)) (Set.Ioc 0 ((b:ℝ)-(v:ℝ))) ∧
      (∫t in Set.Ioc 0 ((b:ℝ)-(v:ℝ)),t^(ρ-1/2)*(∫ω,‖NativeRandomRows.nativeRow (Fields a j 1) (((b:ℝ)-t).toNNReal,ω)-
        NativeRandomRows.nativeRow (Fields a j 2) (((b:ℝ)-t).toNNReal,ω)‖^2 ∂μ))≤
          MixedNativeVarianceGammaTime.constant P A ρ*(CompactMollifier.radius (j+1))^(2*P.exponent+4*ρ)*
            ((b:ℝ)-(v:ℝ))^((P.exponent-1)/2)*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  have hmean:Measurable Cur:=by
    have hs:Measurable (NativeJointGammaCurrent.state UU VV Λ 1 b):=
      ((NativeJointGammaCurrent.state_predictable 𝓕 UU VV S.first_predictable S.second_predictable Λ 1 b).mono
        (predictable_le_product 𝓕)).measurable
    exact (PredictableScalarField.nativeField_measurable hs).comp
      (MixedNativeVarianceGammaTime.ageClock_measurable (Ω:=Ω) b)
  have he:=MixedNativeVarianceGammaTime.scalar_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P hΛ v b hvb hbH hH hwindow hsmall Bpast hBDGpast ha hA hρ0 hρ1 hholder Cur hmean j
  have hmem:∀ᵐt∂volume.restrict (Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ))),t∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ)):=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hfun:(fun t=>t^(ρ-1/2)*(∫ω,‖NativeRandomRows.nativeRow (Fields a j 1) (((b:ℝ)-t).toNNReal,ω)-
      NativeRandomRows.nativeRow (Fields a j 2) (((b:ℝ)-t).toNNReal,ω)‖^2 ∂μ))=ᵐ[volume.restrict (Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)))]
        (fun t=>t^(ρ-1/2)*(∫z,|Grad a j Cur (t,z)|^2 ∂μ.prod haarAddCircle)):=by
    filter_upwards [hmem] with t ht
    rw [current_sample 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hvb hbH hH
      ha hA hholder hnull B0 B1 hBDG0 hBDG1 j t ht]
  exact ⟨he.1.congr hfun.symm,(integral_congr_ae hfun).trans_le he.2⟩

include hvb in
/-- Exact expected native-row energy, with the original sample and spatial measures. -/
theorem reference_sample {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A:ℝ} (hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (j:ℕ) (t:ℝ) (ht:t∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))):
    (∫ω,‖NativeRandomRows.nativeRow (Fields a j 4) (((b:ℝ)-t).toNNReal,ω)-
      NativeRandomRows.nativeRow (Fields a j 5) (((b:ℝ)-t).toNNReal,ω)‖^2 ∂μ)=
        ∫z,|Grad a j Ref (t,z)|^2 ∂μ.prod haarAddCircle:=by
  have hm(i:Fin 6):Measurable (Fields a j i):=
    MixedNativeJointRowFields.fields_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
      v b hvb hbH hH hnull B0 B1 hBDG0 hBDG1 a ha j i
  have hb(i:Fin 6)(p:ℝ≥0×Ω)(x:HeatCircle):‖Fields a j i (p,x)‖≤ScalarHeatSingleMultiplier.cap A P.exponent j:=
    MixedNativeJointRowFields.fields_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
      v b hbH hH ha hA hholder j i p x
  rw [(NativeRowProductEnergy.difference μ (Fields a j 4) (Fields a j 5) (hm 4) (hm 5) (hb 4) (hb 5) _).2]
  exact integral_congr_ae (ae_of_all _ (fun z=>reference_point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
    v b hbH hH a j t ht z))

include hIJ₀ hIJ₁ hΛ hH hvb hbH hwindow hsmall hBDGpast in
/-- The ACTUAL reference variance-change row has the sharp future-time gain.
No independent-mean or past-moment budget is assumed. -/
theorem reference_energy {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (j:ℕ):
    IntegrableOn (fun t=>t^(ρ-1/2)*(∫ω,‖NativeRandomRows.nativeRow (Fields a j 4) (((b:ℝ)-t).toNNReal,ω)-
      NativeRandomRows.nativeRow (Fields a j 5) (((b:ℝ)-t).toNNReal,ω)‖^2 ∂μ)) (Set.Ioc 0 ((b:ℝ)-(v:ℝ))) ∧
      (∫t in Set.Ioc 0 ((b:ℝ)-(v:ℝ)),t^(ρ-1/2)*(∫ω,‖NativeRandomRows.nativeRow (Fields a j 4) (((b:ℝ)-t).toNNReal,ω)-
        NativeRandomRows.nativeRow (Fields a j 5) (((b:ℝ)-t).toNNReal,ω)‖^2 ∂μ))≤
          MixedNativeVarianceGammaTime.constant P A ρ*(CompactMollifier.radius (j+1))^(2*P.exponent+4*ρ)*
            ((b:ℝ)-(v:ℝ))^((P.exponent-1)/2)*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  have hmean:Measurable Ref:=MixedNativeVarianceGammaTime.referenceMean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
    v b hvb hbH hH hnull B0 B1 hBDG0 hBDG1
  have he:=MixedNativeVarianceGammaTime.scalar_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P hΛ v b hvb hbH hH hwindow hsmall Bpast hBDGpast ha hA hρ0 hρ1 hholder Ref hmean j
  have hmem:∀ᵐt∂volume.restrict (Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ))),t∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ)):=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hfun:(fun t=>t^(ρ-1/2)*(∫ω,‖NativeRandomRows.nativeRow (Fields a j 4) (((b:ℝ)-t).toNNReal,ω)-
      NativeRandomRows.nativeRow (Fields a j 5) (((b:ℝ)-t).toNNReal,ω)‖^2 ∂μ))=ᵐ[volume.restrict (Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)))]
        (fun t=>t^(ρ-1/2)*(∫z,|Grad a j Ref (t,z)|^2 ∂μ.prod haarAddCircle)):=by
    filter_upwards [hmem] with t ht
    rw [reference_sample 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hvb hbH hH
      ha hA hholder hnull B0 B1 hBDG0 hBDG1 j t ht]
  exact ⟨he.1.congr hfun.symm,(integral_congr_ae hfun).trans_le he.2⟩

end SHE.MixedNativeJointVarianceRows
