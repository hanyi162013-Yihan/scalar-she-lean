module

public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeJointPhysicalRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance nativeJointPhysicalRows_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointPhysicalRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointPhysicalRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointPhysicalRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointPhysicalRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointPhysicalRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)

def additiveRow (p : ℝ≥0×Ω) (i : Fin n) : RealHaarInput :=
  NativeObservationCovariance.row hκ (AdditiveHaarForcing.constantField κ hκ) (Z i).target (p.1:ℝ) (Z i).center

def firstRow (p : ℝ≥0×Ω) (i : Fin n) : RealHaarInput :=
  NativeObservationCovariance.row hell (ContinuousHeatMild.coefficientFunction haU hell hbU S.first p)
    (Z i).target (p.1:ℝ) (Z i).center

def secondRow (p : ℝ≥0×Ω) (i : Fin n) : RealHaarInput :=
  NativeObservationCovariance.row hell (ContinuousHeatMild.coefficientFunction haV hell hbV S.second p)
    (Z i).target (p.1:ℝ) (Z i).center

def physicalRow (p : ℝ≥0×Ω) (i : Fin n) : Both RealHaarInput :=
  WithLp.toLp 2 (additiveRow κ hκ Z p i,
    secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i+
      (1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))) •
        (firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i-
          secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i))

/-- Actual joint-coordinate rows equal the printed physical common-Haar
rows. Original sigma and target T stay distinct, including future stops
beyond the current covered horizon. -/
theorem rows_ae (hΛ : 0≤Λ) (b : ℝ≥0) (hgap : ∀ i,(b:ℝ)<(Z i).target) :
    ∀ᵐ p ∂energyMeasure μ H,p.1<b → ∀ i,
      MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ i p=
        physicalRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i := by
  let r₀ (i) := NativeObservationProcess.process 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (hgap i) (Z i).center
  let rU (i) := NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (hgap i) (Z i).center
  let rV (i) := NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (hgap i) (Z i).center
  have hg (i) := JointPredictableRows.joint_ae 𝓕 μ H hΛ b (Z i).stop (r₀ i) (rU i) (rV i)
  have h₀ (i) := NativeObservationProcess.process_ae 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (hgap i) (Z i).center
  have hU (i) := NativeObservationProcess.process_ae 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (hgap i) (Z i).center
  have hV (i) := NativeObservationProcess.process_ae 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (hgap i) (Z i).center
  have hR := FiniteItoBlockRows.rows_ae 𝓕 μ H (MixedNativeJointObservations.weights Λ Z)
    (MixedNativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b hgap hΛ)
  filter_upwards [ae_all_iff.mpr hg,ae_all_iff.mpr h₀,ae_all_iff.mpr hU,ae_all_iff.mpr hV,hR]
    with p hg h₀ hU hV hR hp i
  have hh := hg i hp.le
  have hpb : (p.1:ℝ)<(b:ℝ) := by exact_mod_cast hp
  have he₀ := h₀ i
  have heU := hU i
  have heV := hV i
  rw [NativeObservationProcess.integrand_eq hκ _ (hgap i),ite_eq_left hpb] at he₀
  rw [NativeObservationProcess.integrand_eq hell _ (hgap i),ite_eq_left hpb] at heU heV
  change FiniteItoBlockMap.rows 𝓕 μ H _ _ i p=_
  rw [hR i]
  simp only [MixedNativePairExtendedMartingale.rows,Fin.append_left,Fin.append_right,MixedNativeJointObservations.weights]
  change TwoChannelItoRows.block 𝓕 μ H (r₀ i) (rU i) p+Real.exp (-Λ*(Z i).stop) •
    InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b (rU i) (rV i) p=_
  rw [hh]
  change WithLp.toLp 2 (r₀ i p,rV i p+(1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))) • (rU i p-rV i p))=_
  rw [he₀,heU,heV]
  rfl

end SHE.MixedNativeJointPhysicalRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativeJointBracketDefect
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open MixedNativeJointPhysicalRows
open scoped NNReal ENNReal
local instance nativeJointBracketDefect_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointBracketDefect_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointBracketDefect_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointBracketDefect_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointBracketDefect_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointBracketDefect_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)

def physicalGram (p : ℝ≥0×Ω) : Matrix (Fin n) (Fin n) ℝ := fun i j => inner ℝ
  (physicalRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)
  (physicalRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p j)

def baseGram (p : ℝ≥0×Ω) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  inner ℝ (additiveRow κ hκ Z p i) (additiveRow κ hκ Z p j)+
    inner ℝ (secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)
      (secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p j)

def defect (p : ℝ≥0×Ω) : Matrix (Fin n) (Fin n) ℝ :=
  let u := firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p
  let v := secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p
  let r := fun i => 1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))
  fun i j => r i*inner ℝ (u i-v i) (v j)+r j*inner ℝ (v i) (u j-v j)+
    r i*r j*inner ℝ (u i-v i) (u j-v j)

/-- Exact direct bracket defect of the constructed pair, with its two
cross terms and its quadratic common-Haar difference term. -/
theorem physicalGram_eq_base_add_defect (p : ℝ≥0×Ω) :
    physicalGram 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p=
      baseGram 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p+
        defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p := by
  ext i j
  have he := SHE.direct_bracket_defect
    (secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)
    (secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p j)
    (firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i-
      secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)
    (firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p j-
      secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p j)
    (1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))) (1-Real.exp (-Λ*((Z j).stop-(p.1:ℝ))))
  simp only [physicalGram,physicalRow,WithLp.prod_inner_apply,Matrix.add_apply,baseGram,defect]
  linarith

/-- The local part of the same physical Gram is precisely TOTAL
variance kappa+aU(V), with an actual jointly predictable scalar spatial
representative. No residual-only covariance is substituted. -/
theorem baseGram_eq_total_density {δ r : ℝ} (hδ : 0<δ)
    (hgap : ∀ i,δ≤(Z i).target-r) (p : ℝ≥0×Ω) (hpr : (p.1:ℝ)≤r) :
    baseGram 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p=
      CovarianceMatrix.densityMatrix
        (fun tx => κ+aV (PredictableScalarField.wordField (Function.uncurry S.second) p.2 tx)) Z (p.1:ℝ) := by
  have hT (i : Fin n) : (p.1:ℝ)<(Z i).target := by have := hgap i;linarith
  have he := NonlinearTwoChannelStep.density_sum_eq 𝓕 κ hκ hell
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    (Function.uncurry S.second) S.second_predictable aV haV hbV (fun _ => rfl) Z hδ hgap hpr p.2
  rw [← he]
  ext i j
  have h₀ := NativeObservationCovariance.row_cross_covariance hκ (AdditiveHaarForcing.constantField κ hκ)
    Z (p.1:ℝ) i j (hT i) (hT j)
  have hV := NativeObservationCovariance.row_cross_covariance hell
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second p) Z (p.1:ℝ) i j (hT i) (hT j)
  simp only [baseGram,Matrix.add_apply,additiveRow,secondRow]
  rw [h₀,hV]
  simp only [Matrix.add_apply,CovarianceMatrix.densityMatrix,WordRecursion.covarianceDensity,
    NativeItoBracket.coefficient,Real.toNNReal_coe]

end SHE.MixedNativeJointBracketDefect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.MixedNativeJointCovariance
open MeasureTheory Set GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open MixedNativeJointPhysicalRows MixedNativeJointBracketDefect
open scoped NNReal ENNReal
local instance nativeJointCovariance_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointCovariance_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)

theorem rows_ae_real (hΛ : 0≤Λ) (b : ℝ≥0) (hgap : ∀ i,(b:ℝ)<(Z i).target) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),t<(b:ℝ) → ∀ i,
      MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ i (t.toNNReal,ω)=
        physicalRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z (t.toNNReal,ω) i := by
  have hp := MixedNativeJointPhysicalRows.rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b hgap
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  rw [← timeMeasure_map H]
  apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hω] with t ht
  intro htb i
  have hh := ht (by exact_mod_cast htb) i
  simpa only [Prod.swap,Real.toNNReal_coe] using hh

theorem rowCovariance_eq_physicalGram (hΛ : 0≤Λ) (b : ℝ≥0) (hgap : ∀ i,(b:ℝ)<(Z i).target) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),t<(b:ℝ) →
      StandardFiniteIto.rowCovariance 𝓕 μ H
        (MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ) ω t=
      physicalGram 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z (t.toNNReal,ω) := by
  filter_upwards [rows_ae_real 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b hgap] with ω hω
  filter_upwards [hω] with t ht htb
  ext i j
  change inner ℝ
    (MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ i (t.toNNReal,ω))
    (MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ j (t.toNNReal,ω))=_
  rw [ht htb i,ht htb j]
  rfl

/-- The actual joint bracket is local TOTAL variance kappa+aU(V) plus
the literal first-defect matrix. This is derived from the actual common
Haar analysis rows and the scalar coefficient representative. -/
theorem rowCovariance_eq_total_add_defect (hΛ : 0≤Λ) (b : ℝ≥0)
    {δ : ℝ} (hδ : 0<δ) (hgap : ∀ i,δ≤(Z i).target-(b:ℝ)) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),t<(b:ℝ) →
      StandardFiniteIto.rowCovariance 𝓕 μ H
        (MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b
          (fun i => by have := hgap i;linarith) hΛ) ω t=
      CovarianceMatrix.densityMatrix
        (fun tx => κ+aV (PredictableScalarField.wordField (Function.uncurry S.second) ω tx)) Z t+
      defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z (t.toNNReal,ω) := by
  have hstrict : ∀ i,(b:ℝ)<(Z i).target := by intro i;have := hgap i;linarith
  filter_upwards [rowCovariance_eq_physicalGram 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b hstrict] with ω hω
  filter_upwards [hω,ae_restrict_mem measurableSet_Ioc] with t ht htm htb
  rw [ht htb,physicalGram_eq_base_add_defect]
  have he := baseGram_eq_total_density 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hδ hgap
    (t.toNNReal,ω) (by rw [Real.coe_toNNReal _ htm.1.le];exact htb.le)
  simp only [Real.coe_toNNReal _ htm.1.le] at he
  rw [he]

end SHE.MixedNativeJointCovariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.MixedNativeJointPhysicalStep
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open SmoothCylinders FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open GaussianItoTest GaussianTaylorAverage CovarianceEndpoint
open scoped NNReal ENNReal
local instance nativeJointPhysicalStep_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance nativeJointPhysicalStep_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointPhysicalStep_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointPhysicalStep_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointPhysicalStep_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointPhysicalStep_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointPhysicalStep_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- The literal local-insertion/first-defect step for the constructed
native pair. Only the local scalar coefficient is appended as aU new
point leaf; the full common-Haar defect is retained as aU terminating
mark. Original stops and targets are not identified. -/
theorem one_step (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    {n : ℕ} (W : EndpointWindow n) (hleft : 0≤W.left)
    (b : ℝ≥0) (hW : W.right=(b:ℝ)) (hbH : b≤H)
    {δ : ℝ} (hδ : 0<δ) (hgap : ∀ i,δ≤(W.observations i).target-(b:ℝ))
    (hstop : ∀ i,(b:ℝ)≤(W.observations i).stop)
    {F : State n→ℝ} (hF : BoundedSmooth F) :
    let Y := fun (ω : Ω) (t : ℝ) => MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      W.observations b t.toNNReal ω
    ∃ N : Ω→ℝ,Integrable N μ ∧ (∫ ω,N ω ∂μ)=0 ∧ ∀ᵐ ω ∂μ,
      F (Y ω b)=WordRecursion.gaussianSemigroup W.coefficient W.observations W.left W.right F (Y ω W.left)+N ω+
        ∫ t in W.left..W.right,
          (∫ x : HeatCircle,WordRecursion.insertion (fun v => κ+aV v) W.coefficient W.observations t x (backward W F t)
            (JointPhysicalInsertion.appendState
              (PredictableScalarField.wordField (Function.uncurry S.second) ω (t,x)) (Y ω t)) ∂AddCircle.haarAddCircle)+
          (1/2:ℝ)*covarianceAction
            (MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W.observations (t.toNNReal,ω))
            (GaussianTaylor.hessian (backward W F t) (Y ω t)) := by
  intro Y
  have hstrict : ∀ i,(b:ℝ)<(W.observations i).target := by intro i;have := hgap i;linarith
  obtain ⟨N,hNi,hNc,hN⟩ := MixedNativeJointBackwardStep.one_step 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hnull hJ hΛ W hleft b hW hbH hstrict hstop hF
  have hΓ := MixedNativeJointCovariance.rowCovariance_eq_total_add_defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S W.observations hΛ b hδ hgap
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hA : 0≤κ+M := add_nonneg hκ.le hM
  have hbound : ∀ z,|κ+aV z|≤κ+M := by
    intro z
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbV z).1))]
    exact add_le_add le_rfl (hbV z).2
  refine ⟨N,hNi,hNc,?_⟩
  filter_upwards [hN,hΓ] with ω hω hΓ
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le W.ordered,← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hs : Ioo W.left W.right ⊆ Ioc (0:ℝ) (H:ℝ) := by
    intro t ht
    exact ⟨hleft.trans_lt ht.1,ht.2.le.trans (by rw [hW];exact_mod_cast hbH)⟩
  have hΓ' := hΓ.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))
  filter_upwards [hΓ',ae_restrict_mem measurableSet_Ioo] with t ht htm
  have htb : t<(b:ℝ) := by rw [← hW];exact htm.2
  rw [ht htb]
  exact (MixedNativeJointBackwardStep.cancellation W F _ t (Y ω t)).symm.trans
    (JointPhysicalInsertion.insertion_and_defect W (fun v => κ+aV v) (measurable_const.add haV)
      (PredictableScalarField.wordField (Function.uncurry S.second) ω)
      (PredictableScalarField.wordField_section_measurable 𝓕 S.second_predictable ω)
      hA hbound F htm (Y ω t) _)

end SHE.MixedNativeJointPhysicalStep
