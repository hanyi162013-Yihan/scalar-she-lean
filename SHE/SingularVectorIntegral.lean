module

public import SHE.SingularStoppedVersion
public import SHE.FrozenReferenceLaw

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.SingularVectorIntegral
open Set MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H b : ℝ≥0) (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
variable {n : ℕ} (z : WordRecursion.State n) (R : Fin n → Process (E := C) 𝓕 μ H)

def value (p : ℝ≥0 × Ω) : WordRecursion.State n :=
  WithLp.toLp 2 (fun i => z i+SingularStoppedVersion.version 𝓕 μ H b J (R i) p.1 p.2)

theorem continuous_value (hb0 : 0<b) (ω : Ω) :
    Continuous (fun t => value 𝓕 μ H b J z R (t,ω)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_const.add (SingularStoppedVersion.continuous_version 𝓕 μ H b J (R i) hb0 ω)

theorem predictable_value (hbH : b≤H) (hb0 : 0<b)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (K : Fin n → ℝ) (hK : ∀ i,0≤K i)
    (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H, p.1≤b → ‖R i p‖^2≤K i*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ))) :
    StronglyMeasurable[𝓕.predictable] (value 𝓕 μ H b J z R) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  apply Measurable.stronglyMeasurable
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_const.add
    (SingularStoppedVersion.predictable_version 𝓕 μ H b J (R i) hbH hb0 hnull B hBDG (hK i) (hR i)).measurable

theorem integral_representation (hbH : b≤H) (hb0 : 0<b)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (K : Fin n → ℝ) (hK : ∀ i,0≤K i)
    (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H, p.1≤b → ‖R i p‖^2≤K i*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))
    (t : ℝ≥0) (ht : t≤b) :
    (fun ω => value 𝓕 μ H b J z R (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J z R t := by
  have he := ae_all_iff.mpr (fun i =>
    SingularStoppedVersion.version_ae 𝓕 μ H b J (R i) hbH hb0 B hBDG (hK i) (hR i) t)
  filter_upwards [he] with ω hω
  apply PiLp.ext
  intro i
  change z i+SingularStoppedVersion.version 𝓕 μ H b J (R i) t ω=
    z i+J.integral (stop 𝓕 μ H (t:ℝ) (R i)) ω
  rw [hω i,min_eq_left (show (t:ℝ)≤(b:ℝ) by exact_mod_cast ht)]

end SHE.SingularVectorIntegral
