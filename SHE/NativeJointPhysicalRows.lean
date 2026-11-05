module

public import SHE.NativeJointObservations
public import SHE.FiniteItoBlockRows
public import SHE.JointPredictableRows
public import SHE.Algebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.NativeJointPhysicalRows
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
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)

def additiveRow (p : ℝ≥0×Ω) (i : Fin n) : RealHaarInput :=
  NativeObservationCovariance.row hκ (AdditiveHaarForcing.constantField κ hκ) (Z i).target (p.1:ℝ) (Z i).center

def firstRow (p : ℝ≥0×Ω) (i : Fin n) : RealHaarInput :=
  NativeObservationCovariance.row hell (ContinuousHeatMild.coefficientFunction ha hell hb S.first p)
    (Z i).target (p.1:ℝ) (Z i).center

def secondRow (p : ℝ≥0×Ω) (i : Fin n) : RealHaarInput :=
  NativeObservationCovariance.row hell (ContinuousHeatMild.coefficientFunction ha hell hb S.second p)
    (Z i).target (p.1:ℝ) (Z i).center

def physicalRow (p : ℝ≥0×Ω) (i : Fin n) : Both RealHaarInput :=
  WithLp.toLp 2 (additiveRow κ hκ Z p i,
    secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i+
      (1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))) •
        (firstRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i-
          secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i))

/-- Actual joint-coordinate rows equal the printed physical common-Haar
rows. Original sigma and target T stay distinct, including future stops
beyond the current covered horizon. -/
theorem rows_ae (hΛ : 0≤Λ) (b : ℝ≥0) (hgap : ∀ i,(b:ℝ)<(Z i).target) :
    ∀ᵐ p ∂energyMeasure μ H,p.1<b → ∀ i,
      NativeJointObservations.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap hΛ i p=
        physicalRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i := by
  let r₀ (i) := NativeObservationProcess.process 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (hgap i) (Z i).center
  let rU (i) := NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient (hgap i) (Z i).center
  let rV (i) := NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second) S.second_coefficient (hgap i) (Z i).center
  have hg (i) := JointPredictableRows.joint_ae 𝓕 μ H hΛ b (Z i).stop (r₀ i) (rU i) (rV i)
  have h₀ (i) := NativeObservationProcess.process_ae 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (hgap i) (Z i).center
  have hU (i) := NativeObservationProcess.process_ae 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient (hgap i) (Z i).center
  have hV (i) := NativeObservationProcess.process_ae 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second) S.second_coefficient (hgap i) (Z i).center
  have hR := FiniteItoBlockRows.rows_ae 𝓕 μ H (NativeJointObservations.weights Λ Z)
    (NativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
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
  simp only [NativePairExtendedMartingale.rows,Fin.append_left,Fin.append_right,NativeJointObservations.weights]
  change TwoChannelItoRows.block 𝓕 μ H (r₀ i) (rU i) p+Real.exp (-Λ*(Z i).stop) •
    InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b (rU i) (rV i) p=_
  rw [hh]
  change WithLp.toLp 2 (r₀ i p,rV i p+(1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))) • (rU i p-rV i p))=_
  rw [he₀,heU,heV]
  rfl

end SHE.NativeJointPhysicalRows
