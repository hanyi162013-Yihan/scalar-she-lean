module

public import SHE.JointGammaPhysicalRows
public import SHE.JointRescaledRows
public import SHE.FiniteReferenceSpliceRows
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaEndpointCovariance
public import SHE.FiniteAffineRows
public import SHE.PredictableRealSections
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.JointGammaRecursionRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaPhysicalRows_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaPhysicalRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaPhysicalRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaPhysicalRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaPhysicalRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaPhysicalRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaPhysicalRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaPhysicalRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


open Set FiniteCovariancePullback
variable (θ : ℝ)
local notation "R" => FirstGammaEndpointRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH
local notation "Rref" => FirstGammaEndpointRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ
local notation "Raw" => FiniteReferenceSplice.jointRows 𝓕 μ H v R Rref
local notation "Rows" => FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "Frozen" => fun i:Fin n=>TwoChannelItoRows.block 𝓕 μ H
  (FirstGammaEndpointRows.additive 𝓕 μ H κ hκ Z b htarget hbH i)
  (FirstGammaEndpointRows.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ i)
local notation "L" => JointGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "Ref" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)

local notation "r0" => FirstGammaEndpointRows.additive 𝓕 μ H κ hκ Z b htarget hbH
local notation "rU" => FirstGammaEndpointRows.first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH
local notation "rV" => FirstGammaEndpointRows.second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH

/-- Original full-horizon endpoint rows agree with the literal physical
rows simultaneously in every finite coordinate before the root stop. -/
theorem original_rows_ae : ∀ᵐ p∂energyMeasure μ H,p.1<b→∀ i,
    r0 i p=MixedNativeJointPhysicalRows.additiveRow κ hκ Z p i ∧
    rU i p=MixedNativeJointPhysicalRows.firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i ∧
    rV i p=MixedNativeJointPhysicalRows.secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i:=by
  have ha(i:Fin n):=FullHorizonEndpoint.process_ae 𝓕 μ H b hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (htarget i) (Z i).center hbH
  have hu(i:Fin n):=FullHorizonEndpoint.process_ae 𝓕 μ H b hell
    (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient
    (htarget i) (Z i).center hbH
  have hv(i:Fin n):=FullHorizonEndpoint.process_ae 𝓕 μ H b hell
    (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient
    (htarget i) (Z i).center hbH
  filter_upwards [ae_all_iff.mpr ha,ae_all_iff.mpr hu,ae_all_iff.mpr hv] with p ha hu hv hpb i
  have hp:(p.1:ℝ)<(b:ℝ):=by exact_mod_cast hpb
  have hpt:(p.1:ℝ)<(Z i).target:=hp.trans_le (htarget i)
  have hmem:p∈StoppedItoInputs.before (Ω:=Ω) (b:ℝ):=hp
  constructor
  · simpa only [FirstGammaEndpointRows.additive,FullHorizonEndpoint.raw,
      Set.indicator_of_mem hmem,NativeObservationEndpoint.fullIntegrand,if_pos hpt,
      MixedNativeJointPhysicalRows.additiveRow] using ha i
  constructor
  · simpa only [FirstGammaEndpointRows.first,FullHorizonEndpoint.raw,
      Set.indicator_of_mem hmem,NativeObservationEndpoint.fullIntegrand,if_pos hpt,
      MixedNativeJointPhysicalRows.firstRow] using hu i
  · simpa only [FirstGammaEndpointRows.second,FullHorizonEndpoint.raw,
      Set.indicator_of_mem hmem,NativeObservationEndpoint.fullIntegrand,if_pos hpt,
      MixedNativeJointPhysicalRows.secondRow] using hv i

/-- At theta one the finite joint current has precisely the old joint
recursion rows, with the original stopping time retained. -/
theorem current_one_eq_physical (hstop:∀ i,(Z i).stop=(Z i).target):
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀ i,
      mappedRow (JointGammaAffine.current n Λ 1 (fun i=>(Z i).target))
        (fun j=>FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 1 j p) i=
      MixedNativeJointPhysicalRows.physicalRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S Z p i:=by
  have hc:=JointGammaPhysicalRows.current_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 1
  have hr:=original_rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z b htarget hbH
  filter_upwards [hc,hr] with p hc hr hvp hpb i
  rw [hc hvp hpb i,(hr hpb i).1,(hr hpb i).2.1,(hr hpb i).2.2]
  unfold MixedNativeJointPhysicalRows.physicalRow
  rw [hstop i]
  congr 1
  simp only [one_mul,sub_smul,one_smul,smul_sub]
  abel

/-- At theta zero the current rows are genuine ordinary-U rows. -/
theorem current_zero_eq_physical :
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀ i,
      mappedRow (JointGammaAffine.current n Λ 0 (fun i=>(Z i).target))
        (fun j=>FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 0 j p) i=
      WithLp.toLp 2 (MixedNativeJointPhysicalRows.additiveRow κ hκ Z p i,
        MixedNativeJointPhysicalRows.firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S Z p i):=by
  have hc:=JointGammaPhysicalRows.current_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 0
  have hr:=original_rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z b htarget hbH
  filter_upwards [hc,hr] with p hc hr hvp hpb i
  rw [hc hvp hpb i,(hr hpb i).1,(hr hpb i).2.1]
  simp only [zero_mul,sub_zero,one_smul,zero_smul,add_zero]

/-- The actual theta-one finite bracket is the literal ordinary-V
local density plus the full joint defect matrix. -/
theorem one_gram (hstop:∀ i,(Z i).stop=(Z i).target):
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→
      gram (mappedRow (JointGammaAffine.current n Λ 1 (fun i=>(Z i).target))
        (fun j=>FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 1 j p))=
      CovarianceMatrix.densityMatrix
        (fun tx=>κ+aV (PredictableScalarField.wordField (Function.uncurry S.second) p.2 tx)) Z p.1+
        MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S Z p:=by
  have hr:=current_one_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH hstop
  filter_upwards [hr] with p hr hvp hpb
  have hg:gram (mappedRow (JointGammaAffine.current n Λ 1 (fun i=>(Z i).target))
        (fun j=>FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 1 j p))=
      MixedNativeJointBracketDefect.physicalGram 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S Z p:=by
    ext i j
    exact congrArg₂ (inner ℝ) (hr hvp hpb i) (hr hvp hpb j)
  rw [hg,MixedNativeJointBracketDefect.physicalGram_eq_base_add_defect]
  congr 1
  have hδ:0<(b:ℝ)-(p.1:ℝ):=sub_pos.mpr (by exact_mod_cast hpb)
  exact MixedNativeJointBracketDefect.baseGram_eq_total_density 𝓕 μ H Λ κ hκ haU haV
    hell hbU hbV I₀ I₁ u₀ v₀ S Z hδ (fun i=>by linarith [htarget i]) p le_rfl

/-- The actual theta-zero bracket is the independently ordinary-U
local density, not the bracket of a joint theta-zero word process. -/
theorem zero_gram:
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→
      gram (mappedRow (JointGammaAffine.current n Λ 0 (fun i=>(Z i).target))
        (fun j=>FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 0 j p))=
      CovarianceMatrix.densityMatrix
        (fun tx=>κ+aU (PredictableScalarField.wordField (Function.uncurry S.first) p.2 tx)) Z p.1:=by
  have hr:=current_zero_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH
  filter_upwards [hr] with p hr hvp hpb
  have hδ:0<(b:ℝ)-(p.1:ℝ):=sub_pos.mpr (by exact_mod_cast hpb)
  have hgap:∀ i,(b:ℝ)-(p.1:ℝ)≤(Z i).target-(p.1:ℝ):=fun i=>by linarith [htarget i]
  have hT:∀ i,(p.1:ℝ)<(Z i).target:=fun i=>by linarith [htarget i]
  have he:=NonlinearTwoChannelStep.density_sum_eq 𝓕 κ hκ hell
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (Function.uncurry S.first) S.first_predictable aU haU hbU (fun _=>rfl) Z hδ hgap le_rfl p.2
  rw [←he]
  ext i j
  change inner ℝ (mappedRow _ _ i) (mappedRow _ _ j)=_
  rw [hr hvp hpb i,hr hvp hpb j]
  simp only [WithLp.prod_inner_apply,MixedNativeJointPhysicalRows.additiveRow,
    MixedNativeJointPhysicalRows.firstRow,Matrix.add_apply]
  rw [NativeObservationCovariance.row_cross_covariance hκ (AdditiveHaarForcing.constantField κ hκ)
      Z (p.1:ℝ) i j (hT i) (hT j),
    NativeObservationCovariance.row_cross_covariance hell
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first p) Z (p.1:ℝ) i j (hT i) (hT j)]
  simp only [CovarianceMatrix.densityMatrix,WordRecursion.covarianceDensity,
    NativeItoBracket.coefficient,Real.toNNReal_coe]

end SHE.JointGammaRecursionRows
