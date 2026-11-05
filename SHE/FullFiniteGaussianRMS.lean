module
public import SHE.FullFiniteGaussianPrefix
public import SHE.FullFiniteGaussianResidual
public import SHE.RemainderBandSpans
public import SHE.ActualFiniteGaussianComparison
public import SHE.NativeBesselParameterSection
public import SHE.MixedFirstDefectHeatBandBound
public import SHE.MixedFirstDefectFiniteBandEnergy
public import SHE.DefectGapFiniteCoefficient
public import SHE.MixedFirstDefectActualBound
public import SHE.ScalarHeatRootBands
public import SHE.JointGammaRootHilbertPair
public import SHE.MixedFirstDefectNativeBound
public import SHE.MixedFirstDefectEnvelopeIdentity

public import SHE.MixedFirstDefectNormEnvelope
public import SHE.MixedFirstDefectConvolutionTransport
public import SHE.MixedFirstDefectMinkowski
public import SHE.MixedFirstDefectDisintegration
public import SHE.NativeBesselParameterSection
public import SHE.MixedFirstDefectIntegral
public import SHE.MixedJointActiveVolume
public import SHE.MixedFirstDefectRMS
public import SHE.ControlledReferenceFamilyDefectL1
public import SHE.RootHistoryCurrentMeasure
public import SHE.NativeBesselParameterAverageAE
public import SHE.HistoryMeasureGeometry
public import SHE.MixedCanonicalRootFields
public import SHE.DefectRelativeFactor
public import SHE.DefectCombinedTime
public import SHE.NativeBesselFieldAE
public import SHE.NativeSignedHaarProcess
public import SHE.ControlledScalarReference
public import SHE.ControlledThetaDefectEnvelope
public import SHE.MixedJointUncutDefectTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.FullFiniteGaussianRMS
open Set MeasureTheory Real AddCircle StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
  NativeHeatObservation CutoffWordLevel CutoffWordHistories CutoffCarriers ControlledProfile
  ControlledReferenceLevel PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw
open scoped NNReal ENNReal BigOperators
open Classical
local instance mixedFirstDefectRMS_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedFirstDefectRMS_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedFirstDefectRMS_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedFirstDefectRMS_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
local instance :MeasurableSpace RealL2:=borel _
local instance :BorelSpace RealL2:=⟨rfl⟩
open scoped BigOperators
variable (P:CanonicalCovariance.ProfileParameters)(haP:SmoothCylinders.BoundedSmooth P.coefficient)
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a)(J:ℕ)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)
local notation "Terminal" n:max=>ActualTerminalBandField.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (a:=a) (J+n) hL hρ
local notation "Span" n:max=>RemainderBandSpans.span P.exponent (J+n+1)

def error(N n:ℕ):ℝ≥0×Ω→CircleL2:=FullOrdinaryHeatBandError.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP (Span n) (J+n) (N+1) hL ρ hρ.le
local notation "Error"=>error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha J hL hρ

def leaf(N n:ℕ):ℝ≥0×Ω→CircleL2:=FullLeafClockIdentity.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP (Span n) (J+n) (N+1) hL ρ hρ.le
local notation "Leaf"=>leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha J hL hρ

def residual(N:ℕ)(Fr Gm:ℕ→ℝ≥0×Ω→CircleL2)(Rf Nf:ℕ→ℕ→ℝ≥0×Ω→CircleL2)(n:ℕ):ℝ≥0×Ω→CircleL2:=
  FullFiniteGaussianResidual.residual
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (ha:=ha) (j:=J+n) (hL:=hL) (hρ:=hρ) (h:=Span n) (haP:=haP)
    N (Fr n) (Gm n) (fun k=>Rf k n) (fun k=>Nf k n)
local notation "Residual"=>residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha J hL hρ

local instance :SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

private theorem rms_eq {f:ℝ≥0×Ω→CircleL2}(hf:AEStronglyMeasurable f (energyMeasure μ H))
    (hi:Integrable (fun z=>‖f z‖^2) (energyMeasure μ H)):
    Real.sqrt (∫z,‖f z‖^2 ∂energyMeasure μ H)=(eLpNorm f 2 (energyMeasure μ H)).toReal:=by
  let hm:MemLp f 2 (energyMeasure μ H):=(memLp_two_iff_integrable_sq_norm hf).mpr hi
  have he:(∫z,‖f z‖^2 ∂energyMeasure μ H)=‖hm.toLp f‖^2:=by
    rw [realLp_norm_sq]
    exact integral_congr_ae (hm.coeFn_toLp.mono (fun z hz=>congrArg (fun e:CircleL2=>‖e‖^2) hz.symm))
  rw [he,Real.sqrt_sq (norm_nonneg _),Lp.norm_toLp]

private theorem rms_sum {F:ℕ→ℝ≥0×Ω→CircleL2}(L:ℕ)
    (hf:AEStronglyMeasurable (∑n∈Finset.range L,F n) (energyMeasure μ H))
    (hi:Integrable (fun z=>‖∑n∈Finset.range L,F n z‖^2) (energyMeasure μ H)):
    Real.sqrt (∫z,‖∑n∈Finset.range L,F n z‖^2 ∂energyMeasure μ H)=
      (eLpNorm (∑n∈Finset.range L,F n) 2 (energyMeasure μ H)).toReal:=by
  simpa only [Finset.sum_apply] using rms_eq μ H hf (by simpa only [Finset.sum_apply] using hi)

/-- The concrete seven-piece finite stochastic comparison in real RMS form.
Each finite frequency block is kept intact, including the total ordinary error. -/
theorem seven_piece(L N:ℕ)(Fr Gm:ℕ→ℝ≥0×Ω→CircleL2)(Rf Nf:ℕ→ℕ→ℝ≥0×Ω→CircleL2)
    (hmFr:∀n,Measurable (Fr n))(hmGm:∀n,Measurable (Gm n))
    (hmRf:∀k,k<N→∀n,Measurable (Rf k n))(hmNf:∀k,k<N→∀n,Measurable (Nf k n))
    (hiFr:Integrable (fun z=>‖∑n∈Finset.range L,Fr n z‖^2) (energyMeasure μ H))
    (hiGm:Integrable (fun z=>‖∑n∈Finset.range L,Gm n z‖^2) (energyMeasure μ H))
    (hiRf:∀k,k<N→Integrable (fun z=>‖∑n∈Finset.range L,Rf k n z‖^2) (energyMeasure μ H))
    (hiNf:∀k,k<N→Integrable (fun z=>‖∑n∈Finset.range L,Nf k n z‖^2) (energyMeasure μ H))
    (hiMark:Integrable (fun z=>‖∑n∈Finset.range L,Residual N Fr Gm Rf Nf n z‖^2) (energyMeasure μ H))
    (hiError:Integrable (fun z=>‖∑n∈Finset.range L,Error N n z‖^2) (energyMeasure μ H))
    (hiLeaf:Integrable (fun z=>‖∑n∈Finset.range L,Leaf N n z‖^2) (energyMeasure μ H)):
    Integrable (fun z=>‖∑n∈Finset.range L,(Terminal n) z‖^2) (energyMeasure μ H) ∧
    Real.sqrt (∫z,‖∑n∈Finset.range L,(Terminal n) z‖^2 ∂energyMeasure μ H)≤
      Real.sqrt (∫z,‖∑n∈Finset.range L,Fr n z‖^2 ∂energyMeasure μ H)+
      Real.sqrt (∫z,‖∑n∈Finset.range L,Gm n z‖^2 ∂energyMeasure μ H)+
      (∑k∈Finset.range N,Real.sqrt (∫z,‖∑n∈Finset.range L,Rf k n z‖^2 ∂energyMeasure μ H))+
      (∑k∈Finset.range N,Real.sqrt (∫z,‖∑n∈Finset.range L,Nf k n z‖^2 ∂energyMeasure μ H))+
      Real.sqrt (∫z,‖∑n∈Finset.range L,Residual N Fr Gm Rf Nf n z‖^2 ∂energyMeasure μ H)+
      Real.sqrt (∫z,‖∑n∈Finset.range L,Error N n z‖^2 ∂energyMeasure μ H)+
      Real.sqrt (∫z,‖∑n∈Finset.range L,Leaf N n z‖^2 ∂energyMeasure μ H):=by
  have mt:Measurable (∑n∈Finset.range L,Terminal n):=by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum (Finset.range L) (fun n _=>
    ActualTerminalBandField.measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ha (J+n) hL hρ)
  have mf:Measurable (∑n∈Finset.range L,Fr n):=by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum (Finset.range L) (fun n _=>hmFr n)
  have mg:Measurable (∑n∈Finset.range L,Gm n):=by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum (Finset.range L) (fun n _=>hmGm n)
  have mr(k:ℕ)(hk:k<N):Measurable (∑n∈Finset.range L,Rf k n):=by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum (Finset.range L) (fun n _=>hmRf k hk n)
  have mn(k:ℕ)(hk:k<N):Measurable (∑n∈Finset.range L,Nf k n):=by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum (Finset.range L) (fun n _=>hmNf k hk n)
  have mm:Measurable (∑n∈Finset.range L,Residual N Fr Gm Rf Nf n):=by
    rw [Finset.sum_fn]
    apply Finset.measurable_sum
    intro n _
    exact FullFiniteGaussianResidual.measurable
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
      (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (ha:=ha) (j:=J+n) (hL:=hL) (hρ:=hρ) (h:=Span n) (haP:=haP)
      N (Fr n) (Gm n) (fun k=>Rf k n) (fun k=>Nf k n) (hmFr n) (hmGm n)
      (fun k hk=>hmRf k hk n) (fun k hk=>hmNf k hk n)
  have me:Measurable (∑n∈Finset.range L,Error N n):=by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum (Finset.range L) (fun n _=>
    FullOrdinaryHeatBandError.measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP (Span n) (J+n) (N+1) hL ρ hρ.le)
  have ml:Measurable (∑n∈Finset.range L,Leaf N n):=by
    rw [Finset.sum_fn]
    apply Finset.measurable_sum
    intro n _
    exact (MixedNativeFullLeafHilbert.field_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP (Span n)
      (fun _ z=>ScalarHeatBands.band a (J+n+1) (z 0))
      (UniformSmooth.UniformBoundedSmooth.fixed ((ScalarHeatBands.band_boundedSmooth ha (J+n+1)).comp_right (EuclideanSpace.proj (0:Fin 1))))
      (((ScalarHeatBands.band_boundedSmooth ha (J+n+1)).comp_right (EuclideanSpace.proj (0:Fin 1))).smooth.continuous.measurable.comp measurable_snd)
      hL hρ.le (N+1)).comp (NNReal.continuous_coe.measurable.prodMap measurable_id)
  have fmem:MemLp (∑n∈Finset.range L,Fr n) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm mf.aestronglyMeasurable).mpr (by simpa only [Finset.sum_apply] using hiFr)
  have gmem:MemLp (∑n∈Finset.range L,Gm n) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm mg.aestronglyMeasurable).mpr (by simpa only [Finset.sum_apply] using hiGm)
  have rmem(k:ℕ)(hk:k<N):MemLp (∑n∈Finset.range L,Rf k n) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm (mr k hk).aestronglyMeasurable).mpr (by simpa only [Finset.sum_apply] using hiRf k hk)
  have nmem(k:ℕ)(hk:k<N):MemLp (∑n∈Finset.range L,Nf k n) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm (mn k hk).aestronglyMeasurable).mpr (by simpa only [Finset.sum_apply] using hiNf k hk)
  have mmem:MemLp (∑n∈Finset.range L,Residual N Fr Gm Rf Nf n) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm mm.aestronglyMeasurable).mpr (by simpa only [Finset.sum_apply] using hiMark)
  have emem:MemLp (∑n∈Finset.range L,Error N n) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm me.aestronglyMeasurable).mpr (by simpa only [Finset.sum_apply] using hiError)
  have lmem:MemLp (∑n∈Finset.range L,Leaf N n) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm ml.aestronglyMeasurable).mpr (by simpa only [Finset.sum_apply] using hiLeaf)
  have hb:=FullFiniteGaussianPrefix.seven_piece
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha J hL hρ L N Fr Gm Rf Nf
  have hfin:(eLpNorm (∑n∈Finset.range L,Fr n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Gm n) 2 (energyMeasure μ H)+
      (∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Rf k n) 2 (energyMeasure μ H))+
      (∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Nf k n) 2 (energyMeasure μ H))+
      eLpNorm (∑n∈Finset.range L,Residual N Fr Gm Rf Nf n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Error N n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Leaf N n) 2 (energyMeasure μ H))≠∞:=by
    simp only [ENNReal.add_ne_top,ENNReal.sum_ne_top]
    exact ⟨⟨⟨⟨⟨⟨fmem.eLpNorm_ne_top,gmem.eLpNorm_ne_top⟩,
      fun k hk=>(rmem k (Finset.mem_range.mp hk)).eLpNorm_ne_top⟩,
      fun k hk=>(nmem k (Finset.mem_range.mp hk)).eLpNorm_ne_top⟩,
      mmem.eLpNorm_ne_top⟩,emem.eLpNorm_ne_top⟩,lmem.eLpNorm_ne_top⟩
  have tm:MemLp (∑n∈Finset.range L,Terminal n) 2 (energyMeasure μ H):=
    lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hfin)
  have ti:Integrable (fun z=>‖∑n∈Finset.range L,(Terminal n) z‖^2) (energyMeasure μ H):=
    by simpa only [Finset.sum_apply] using (memLp_two_iff_integrable_sq_norm mt.aestronglyMeasurable).mp tm
  refine ⟨ti,?_⟩
  have hr:=ENNReal.toReal_mono hfin hb
  have hrf:(∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Rf k n) 2 (energyMeasure μ H))≠∞:=
    ENNReal.sum_ne_top.mpr (fun k hk=>(rmem k (Finset.mem_range.mp hk)).eLpNorm_ne_top)
  have hnf:(∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Nf k n) 2 (energyMeasure μ H))≠∞:=
    ENNReal.sum_ne_top.mpr (fun k hk=>(nmem k (Finset.mem_range.mp hk)).eLpNorm_ne_top)
  have hsumReal:
      (eLpNorm (∑n∈Finset.range L,Fr n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Gm n) 2 (energyMeasure μ H)+
      (∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Rf k n) 2 (energyMeasure μ H))+
      (∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Nf k n) 2 (energyMeasure μ H))+
      eLpNorm (∑n∈Finset.range L,Residual N Fr Gm Rf Nf n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Error N n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Leaf N n) 2 (energyMeasure μ H)).toReal≤
      (eLpNorm (∑n∈Finset.range L,Fr n) 2 (energyMeasure μ H)).toReal+
      (eLpNorm (∑n∈Finset.range L,Gm n) 2 (energyMeasure μ H)).toReal+
      (∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Rf k n) 2 (energyMeasure μ H)).toReal+
      (∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Nf k n) 2 (energyMeasure μ H)).toReal+
      (eLpNorm (∑n∈Finset.range L,Residual N Fr Gm Rf Nf n) 2 (energyMeasure μ H)).toReal+
      (eLpNorm (∑n∈Finset.range L,Error N n) 2 (energyMeasure μ H)).toReal+
      (eLpNorm (∑n∈Finset.range L,Leaf N n) 2 (energyMeasure μ H)).toReal:=by
    have h2(a b:ℝ≥0∞):(a+b).toReal≤a.toReal+b.toReal:=ENNReal.toReal_add_le
    calc
      _≤_:=h2 _ _
      _≤_:=add_le_add_left (h2 _ _) _
      _≤_:=add_le_add_left (add_le_add_left (h2 _ _) _) _
      _≤_:=add_le_add_left (add_le_add_left (add_le_add_left (h2 _ _) _) _) _
      _≤_:=add_le_add_left (add_le_add_left (add_le_add_left (add_le_add_left (h2 _ _) _) _) _) _
      _≤_:=add_le_add_left (add_le_add_left (add_le_add_left (add_le_add_left (add_le_add_left (h2 _ _) _) _) _) _) _
  have hr:=hr.trans hsumReal
  rw [ENNReal.toReal_sum (fun k hk=>(rmem k (Finset.mem_range.mp hk)).eLpNorm_ne_top),
    ENNReal.toReal_sum (fun k hk=>(nmem k (Finset.mem_range.mp hk)).eLpNorm_ne_top)] at hr
  rw [rms_sum μ H L mt.aestronglyMeasurable ti,rms_sum μ H L mf.aestronglyMeasurable hiFr,
    rms_sum μ H L mg.aestronglyMeasurable hiGm,rms_sum μ H L mm.aestronglyMeasurable hiMark,
    rms_sum μ H L me.aestronglyMeasurable hiError,rms_sum μ H L ml.aestronglyMeasurable hiLeaf]
  have hRs:(∑k∈Finset.range N,Real.sqrt (∫z,‖∑n∈Finset.range L,Rf k n z‖^2 ∂energyMeasure μ H))=
      ∑k∈Finset.range N,(eLpNorm (∑n∈Finset.range L,Rf k n) 2 (energyMeasure μ H)).toReal:=
    Finset.sum_congr rfl (fun k hk=>rms_sum μ H L (mr k (Finset.mem_range.mp hk)).aestronglyMeasurable (hiRf k (Finset.mem_range.mp hk)))
  have hNs:(∑k∈Finset.range N,Real.sqrt (∫z,‖∑n∈Finset.range L,Nf k n z‖^2 ∂energyMeasure μ H))=
      ∑k∈Finset.range N,(eLpNorm (∑n∈Finset.range L,Nf k n) 2 (energyMeasure μ H)).toReal:=
    Finset.sum_congr rfl (fun k hk=>rms_sum μ H L (mn k (Finset.mem_range.mp hk)).aestronglyMeasurable (hiNf k (Finset.mem_range.mp hk)))
  rw [hRs,hNs]
  exact hr
end SHE.FullFiniteGaussianRMS
