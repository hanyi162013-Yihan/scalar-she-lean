module

public import SHE.FullHorizonEndpoint
public import SHE.PredictableRealSections
public import SHE.NativeItoBracket

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FullHorizonCovariance
open Set MeasureTheory PredictableL2 StoppedItoInputs FiniteHaar StoppedFourier
open NativeObservationEndpoint NativeObservationProcess NativeObservationCovariance
open scoped NNReal ENNReal
local instance fullHorizonCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance fullHorizonCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)
local notation "R" => fun i:Fin n=>FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf (htarget i) (Z i).center hbH

/-- The original full-H singular endpoint rows have the true physical
cross covariance on one original sample/time event, without any positive
terminal gap or independent-copy premise. -/
theorem rowCovariance_eq_density :
    ∀ᵐ ω∂μ,∀ᵐ t:ℝ∂volume.restrict (Ioc (0:ℝ) (b:ℝ)),
      StandardFiniteIto.rowCovariance 𝓕 μ H R ω t=
        CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t := by
  have he : ∀ᵐ p∂energyMeasure μ H,p.1<b→∀ i,
      R i p=NativeObservationCovariance.row hell (f p) (Z i).target p.1 (Z i).center := by
    filter_upwards [ae_all_iff.mpr (fun i=>FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM f hf (htarget i) (Z i).center hbH)] with p hp hpb i
    rw [hp i]
    have hpb' : (p.1:ℝ)<(b:ℝ):=by exact_mod_cast hpb
    simp only [FullHorizonEndpoint.raw,indicator_of_mem (show p∈before (Ω:=Ω) (b:ℝ) from hpb'),
      fullIntegrand,ite_eq_left (hpb'.trans_le (htarget i))]
  have hr:=PredictableRealSections.of_energy_ae μ H he (0:ℝ) b le_rfl b.2 (by exact_mod_cast hbH)
  filter_upwards [hr] with ω hr
  filter_upwards [hr,ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t hr ht hne
  have ht0 : 0≤t:=ht.1.le
  have htb : t<(b:ℝ):=lt_of_le_of_ne ht.2 hne
  have htbNN : t.toNNReal<b:=by
    change (t.toNNReal:ℝ)<(b:ℝ)
    rwa [Real.coe_toNNReal _ ht0]
  ext i j
  change inner ℝ (R i (t.toNNReal,ω)) (R j (t.toNNReal,ω))=_
  rw [hr htbNN i,hr htbNN j]
  simp only [Real.coe_toNNReal _ ht0]
  simpa only [CovarianceMatrix.densityMatrix,WordRecursion.covarianceDensity,NativeItoBracket.coefficient] using
    row_cross_covariance hell (f (t.toNNReal,ω)) Z t i j (htb.trans_le (htarget i)) (htb.trans_le (htarget j))

end SHE.FullHorizonCovariance
