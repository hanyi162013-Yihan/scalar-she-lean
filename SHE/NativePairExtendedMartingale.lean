module

public import SHE.NativePairLocalMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section

namespace SHE.NativePairExtendedMartingale
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance nativePairExtendedMartingale_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairExtendedMartingale_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairExtendedMartingale_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairExtendedMartingale_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairExtendedMartingale_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairExtendedMartingale_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable {n : ℕ} (target : Fin n→ℝ) (centers : Fin n→HeatCircle) (b : ℝ≥0)
variable (hgap : ∀ i,(b:ℝ)<target i)

def value (t : ℝ≥0) (ω : Ω) : WordRecursion.State (n+n) :=
  WithLp.toLp 2 (Fin.append
    (fun i => PositiveGapObservations.coordinate (target i-(b:ℝ)) (target i) (centers i)
      (Function.uncurry S.first) (min t b,ω))
    (fun i => NativePairLocalMartingale.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b (target i) (centers i) t ω))

def initial : WordRecursion.State (n+n) :=
  WithLp.toLp 2 (Fin.append (fun i => functional (target i) (centers i) u₀)
    (fun i => functional (target i) (centers i) (v₀-u₀)))

def rows (hΛ : 0≤Λ) : Fin (n+n)→Process (E := Both RealHaarInput) 𝓕 μ H :=
  Fin.append
    (fun i => NativePairObservedFirst.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b (hgap i) (centers i))
    (fun i => NativeHybridInput.rightLift 𝓕 μ H
      (NativePairLocalMartingale.row 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b (hgap i) (centers i)))

theorem continuous_value (ω : Ω) :
    Continuous (fun t => value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b t ω) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+n) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have ht : Continuous (fun t : ℝ≥0 => min t b) := continuous_id.min continuous_const
    simpa only [Fin.append_left,Function.comp_def] using
      (PositiveGapObservations.coordinate_continuous (target j-(b:ℝ)) (target j) (centers j)
        (Function.uncurry S.first) (S.first_continuous ω)).comp ht
  · simpa only [Fin.append_right] using NativePairLocalMartingale.continuous_value
      𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b (target j) (centers j) ω

theorem right_stop_integral (t : ℝ) (v : Process (E := RealHaarInput) 𝓕 μ H) :
    J.integral (stop 𝓕 μ H t (NativeHybridInput.rightLift 𝓕 μ H v))=
      (rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H t v) := by
  unfold NativeHybridInput.rightLift
  rw [← RotatedItoAlgebra.map_stop]
  rfl

include hIJ₀ hIJ₁ in
/-- One actual 2n-dimensional continuous martingale records both the
uncontrolled heat observations and the exponentially rescaled controlled
differences. All coordinates use one fixed full-horizon scalar integral. -/
theorem integral_representation (hΛ : 0≤Λ) (hbH : b≤H) (t : ℝ≥0) :
    value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b t=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (initial u₀ v₀ target centers)
        (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b hgap hΛ) t := by
  have hU (i : Fin n) :
      (fun ω => PositiveGapObservations.coordinate (target i-(b:ℝ)) (target i) (centers i)
        (Function.uncurry S.first) (min t b,ω))=ᵐ[μ]
      fun ω => functional (target i) (centers i) u₀+J.integral
        (stop 𝓕 μ H (t:ℝ)
          (NativePairObservedFirst.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b (hgap i) (centers i))) ω := by
    have hT : ((min t b:ℝ≥0):ℝ)<target i :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right t b) (hgap i)
    have hs : stop 𝓕 μ H (t:ℝ)
        (NativePairObservedFirst.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b (hgap i) (centers i))=
      NativePairObservedFirst.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S (min t b) hT (centers i) := by
      rw [NativePairObservedFirst.rows,TwoChannelItoRows.stop_block,
        LocalNativeObservations.stop_observation_process,LocalNativeObservations.stop_observation_process]
      rfl
    filter_upwards [NativePairObservedFirst.observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      (min t b) ((min_le_right t b).trans hbH) hT (centers i)] with ω hω
    rw [PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _
      (sub_le_sub_left (by exact_mod_cast min_le_right t b) (target i)),hs]
    exact hω
  have hD (i : Fin n) := NativePairLocalMartingale.value_representation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ b hbH (hgap i) (centers i) t
  filter_upwards [ae_all_iff.mpr hU,ae_all_iff.mpr hD] with ω hU hD
  apply PiLp.ext
  intro i
  simp only [value,initial,rows,StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using hU j
  · simp only [Fin.append_right]
    rw [right_stop_integral 𝓕 μ H J]
    exact hD j

include hIJ₀ hIJ₁ hgap in
theorem predictable_value (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hΛ : 0≤Λ) (hbH : b≤H) :
    StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b)) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull
  · intro t
    obtain ⟨V,hV,he⟩ := StoppedIntegralVersions.vectorIntegral_adapted_version 𝓕 μ H J
      (initial u₀ v₀ target centers) (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b hgap hΛ) t
    exact ⟨V,hV,(integral_representation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      target centers b hgap hΛ hbH t).trans he⟩
  · exact continuous_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b

end SHE.NativePairExtendedMartingale
