module
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

namespace SHE.FullFiniteGaussianPrefix
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

/-- Actual finite high-band comparison, with one common terminal band
at every recursion depth and the TOTAL ordinary error kept unsquared. -/
theorem seven_piece(L N:ℕ)(Fr Gm:ℕ→ℝ≥0×Ω→CircleL2)(Rf Nf:ℕ→ℕ→ℝ≥0×Ω→CircleL2):
    eLpNorm (∑n∈Finset.range L,Terminal n) 2 (energyMeasure μ H)≤
      eLpNorm (∑n∈Finset.range L,Fr n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Gm n) 2 (energyMeasure μ H)+
      (∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Rf k n) 2 (energyMeasure μ H))+
      (∑k∈Finset.range N,eLpNorm (∑n∈Finset.range L,Nf k n) 2 (energyMeasure μ H))+
      eLpNorm (∑n∈Finset.range L,Residual N Fr Gm Rf Nf n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Error N n) 2 (energyMeasure μ H)+
      eLpNorm (∑n∈Finset.range L,Leaf N n) 2 (energyMeasure μ H):=by
  let T:Fin 7→(ℝ≥0×Ω)→CircleL2:=![∑n∈Finset.range L,Fr n,-(∑n∈Finset.range L,Gm n),
    ∑k∈Finset.range N,∑n∈Finset.range L,Rf k n,∑k∈Finset.range N,∑n∈Finset.range L,Nf k n,
    ∑n∈Finset.range L,Residual N Fr Gm Rf Nf n,-(∑n∈Finset.range L,Error N n),∑n∈Finset.range L,Leaf N n]
  have he:(∑n∈Finset.range L,Terminal n)=∑i:Fin 7,T i:=by
    funext z
    have hd(n:ℕ):(Terminal n) z=Fr n z-Gm n z+(∑k∈Finset.range N,Rf k n z)+
        (∑k∈Finset.range N,Nf k n z)+Residual N Fr Gm Rf Nf n z-Error N n z+Leaf N n z:=by
      dsimp only [residual,FullFiniteGaussianResidual.residual,error,leaf]
      abel
    simp only [T,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,
      Finset.sum_empty,add_zero,Finset.sum_apply,Pi.neg_apply]
    simp_rw [hd]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s:=Finset.range L) (t:=Finset.range N) (f:=fun n k=>Rf k n z),
      Finset.sum_comm (s:=Finset.range L) (t:=Finset.range N) (f:=fun n k=>Nf k n z)]
    abel
  calc
    _=eLpNorm (∑i:Fin 7,T i) 2 (energyMeasure μ H):=congrArg (fun f=>eLpNorm f 2 (energyMeasure μ H)) he
    _≤∑i:Fin 7,eLpNorm (T i) 2 (energyMeasure μ H):=eLpNorm_sum_le (by norm_num)
    _≤_:=by
      simp only [T,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,
        Finset.sum_empty,add_zero,eLpNorm_neg,add_assoc]
      gcongr
      all_goals exact eLpNorm_sum_le (μ:=energyMeasure μ H) (p:=2) (by norm_num)
end SHE.FullFiniteGaussianPrefix
