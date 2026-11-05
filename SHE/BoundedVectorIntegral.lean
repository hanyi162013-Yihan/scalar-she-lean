module

public import SHE.BoundedStoppedVersion
public import SHE.FrozenReferenceLaw

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.BoundedVectorIntegral
open Set MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
variable {n : ℕ} (z : WordRecursion.State n) (R : Fin n → Process (E := C) 𝓕 μ H)

def value (p : ℝ≥0 × Ω) : WordRecursion.State n :=
  WithLp.toLp 2 (fun i => z i+BoundedStoppedVersion.version 𝓕 μ H J (R i) p.1 p.2)

theorem continuous_value (hH0 : 0<H) (ω : Ω) :
    Continuous (fun t => value 𝓕 μ H J z R (t,ω)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_const.add (BoundedStoppedVersion.continuous_version 𝓕 μ H J (R i) hH0 ω)

theorem predictable_value (hH : (H:ℝ)≤1) (hH0 : 0<H)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (K : Fin n → ℝ) (hK : ∀ i,0≤K i)
    (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H, ‖R i p‖^2≤K i) :
    StronglyMeasurable[𝓕.predictable] (value 𝓕 μ H J z R) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  apply Measurable.stronglyMeasurable
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_const.add
    (BoundedStoppedVersion.predictable_version 𝓕 μ H J (R i) hH hH0 hnull B hBDG (hK i) (hR i)).measurable

theorem integral_representation (hH : (H:ℝ)≤1) (hH0 : 0<H)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (K : Fin n → ℝ) (hK : ∀ i,0≤K i)
    (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H, ‖R i p‖^2≤K i)
    (t : ℝ≥0) (ht : t≤H) :
    (fun ω => value 𝓕 μ H J z R (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J z R t := by
  have he := ae_all_iff.mpr (fun i =>
    BoundedStoppedVersion.version_ae 𝓕 μ H J (R i) hH hH0 B hBDG (hK i) (hR i) t)
  filter_upwards [he] with ω hω
  apply PiLp.ext
  intro i
  change z i+BoundedStoppedVersion.version 𝓕 μ H J (R i) t ω=
    z i+J.integral (stop 𝓕 μ H (t:ℝ) (R i)) ω
  rw [hω i,min_eq_left (show (t:ℝ)≤(H:ℝ) by exact_mod_cast ht)]

/-- Bounded original-noise rows have an actual continuous predictable
integral version. Matching their physical covariance identifies its
Gaussian law, without assuming a Gaussian law OR a continuous version as
an additional stochastic input. -/
theorem gaussian_law (hH : (H:ℝ)≤1) (hH0 : 0<H)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (K : Fin n → ℝ) (hK : ∀ i,0≤K i)
    (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H, ‖R i p‖^2≤K i)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J)
    (W : CovarianceEndpoint.EndpointWindow n) (b : ℝ≥0)
    (hv : W.left=0) (hb : W.right=(b:ℝ)) (hbH : b≤H)
    (hcov : ∀ᵐ ω ∂μ,∀ᵐ t : ℝ,t∈Ioo W.left W.right →
      StandardFiniteIto.rowCovariance 𝓕 μ H R ω t=
        CovarianceMatrix.densityMatrix W.coefficient W.observations t) :
    ProbabilityTheory.HasLaw (fun ω => value 𝓕 μ H J z R (b,ω))
      ((ProbabilityTheory.multivariateGaussian 0 (W.path W.left).val).map (fun y => z+y)) μ := by
  have hY := predictable_value 𝓕 μ H J z R hH hH0 hnull B hBDG K hK hR
  apply FrozenReferenceIto.gaussian_law 𝓕 μ H J R z (value 𝓕 μ H J z R) hY hJ hlocal
    (continuous_value 𝓕 μ H J z R hH0)
    (integral_representation 𝓕 μ H J z R hH hH0 B hBDG K hK hR)
    W 0 b (by simpa using hv) hb hbH hcov z
  filter_upwards [integral_representation 𝓕 μ H J z R hH hH0 B hBDG K hK hR 0 (show (0:ℝ≥0)≤H from zero_le),
    ae_all_iff.mpr (fun _i : Fin n => Lp.coeFn_zero ℝ 2 μ)] with ω hω hzero
  rw [hω]
  apply PiLp.ext
  intro i
  change z i+J.integral (stop 𝓕 μ H 0 (R i)) ω=z i
  rw [stop_zero,map_zero]
  exact add_eq_left.mpr (hzero i)

end SHE.BoundedVectorIntegral
