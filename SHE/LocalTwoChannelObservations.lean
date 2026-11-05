module

public import SHE.TwoChannelItoRows
public import SHE.LocalNativeObservationIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.LocalTwoChannelObservations
open MeasureTheory Set PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
open NativeHeatObservation NativeObservationNaturality WordRecursion StoppedItoInputs OrthogonalItoChannels
open scoped NNReal ENNReal
local instance localTwoChannelObservations_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance localTwoChannelObservations_realSigma : MeasurableSpace RealL2 := borel _
local instance localTwoChannelObservations_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance localTwoChannelObservations_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance localTwoChannelObservations_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance localTwoChannelObservations_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance localTwoChannelObservations_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell₀ M₀ ell₁ M₁ : ℝ} (hell₀ : 0 < ell₀) (hM₀ : 0 ≤ M₀)
variable (f₀ : ℝ≥0 × Ω → EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell₁ : 0 < ell₁) (hM₁ : 0 ≤ M₁)
variable (f₁ : ℝ≥0 × Ω → EllipticField ell₁ M₁) (hf₁ : StronglyMeasurable[𝓕.predictable] f₁)
variable {n : ℕ} (Z : Fin n → Observation) (b : ℝ≥0)
variable {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(b:ℝ))

def rows : Fin n → Process (E := Both RealHaarInput) 𝓕 μ h := fun i =>
  TwoChannelItoRows.block 𝓕 μ h
    (LocalNativeObservations.rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ Z b hδ hgap i)
    (LocalNativeObservations.rows 𝓕 μ h hell₁ hM₁ f₁ hf₁ Z b hδ hgap i)

include hM₀ hf₀ hM₁ hf₁ hδ hgap in
/-- The true native observation representation for the sum of two
stochastic channels. Both original-target rows are retained in the block
Hilbert noise, with no conversion to a total-variance Haar factor. -/
theorem integral_representation
    (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ h J))
    (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ h J))
    (u : RealL2) (U : ℝ≥0 × Ω → RealL2)
    (v₀ v₁ : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv₀ : ∀ t : ℝ≥0,t ≤ h → v₀ t=ᵐ[energyMeasure μ h]
      (fun p => kernel ell₀ M₀ hell₀ ((t:ℝ)-(p.1:ℝ),f₀ p)))
    (hv₁ : ∀ t : ℝ≥0,t ≤ h → v₁ t=ᵐ[energyMeasure μ h]
      (fun p => kernel ell₁ M₁ hell₁ ((t:ℝ)-(p.1:ℝ),f₁ p)))
    (hmild : ∀ t : ℝ≥0,t ≤ h → ∀ᵐ ω ∂μ,U (t,ω)=
      NativeHeatObservation.heat (t:ℝ) u+I₀.integral (v₀ t) ω+I₁.integral (v₁ t) ω)
    (hb : b ≤ h) (t : ℝ≥0) :
    (fun ω => LocalNativeObservations.stoppedValue δ Z U b (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ h J (PositiveGapObservations.initial Z u)
        (rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ Z b hδ hgap) t := by
  have hrt : min t b ≤ h := (min_le_right t b).trans hb
  have htarget (i : Fin n) : ((min t b:ℝ≥0):ℝ) < (Z i).target := by
    have hmin : ((min t b:ℝ≥0):ℝ) ≤ b := by exact_mod_cast min_le_right t b
    have := hgap i
    linarith
  have h₀ (i : Fin n) := observe_terminal_integral I₀ (leftIntegral 𝓕 μ h J) hIJ₀
    hell₀ hM₀ f₀ hf₀ (htarget i) (Z i).center (v₀ (min t b)) (hv₀ _ hrt)
  have h₁ (i : Fin n) := observe_terminal_integral I₁ (rightIntegral 𝓕 μ h J) hIJ₁
    hell₁ hM₁ f₁ hf₁ (htarget i) (Z i).center (v₁ (min t b)) (hv₁ _ hrt)
  have hblock (i : Fin n) := TwoChannelItoRows.integral_stop_block_ae 𝓕 μ h J (t:ℝ)
    (LocalNativeObservations.rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ Z b hδ hgap i)
    (LocalNativeObservations.rows 𝓕 μ h hell₁ hM₁ f₁ hf₁ Z b hδ hgap i)
  filter_upwards [hmild _ hrt,ae_all_iff.mpr h₀,ae_all_iff.mpr h₁,ae_all_iff.mpr hblock]
    with ω hU h₀ h₁ hblock
  ext i
  change PositiveGapObservations.coordinate δ (Z i).target (Z i).center U (min t b,ω)=
    functional (Z i).target (Z i).center u+
      J.integral (stop 𝓕 μ h t (rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ Z b hδ hgap i)) ω
  have hg : δ ≤ (Z i).target-((min t b:ℝ≥0):ℝ) :=
    (hgap i).trans (sub_le_sub_left (by exact_mod_cast min_le_right t b) _)
  rw [PositiveGapObservations.coordinate_eq_functional hδ U _ _ hg,hU,map_add,map_add]
  dsimp only [Prod.fst]
  rw [NativeHeatObservation.functional_heat (τ := (Z i).target-((min t b:ℝ≥0):ℝ))
    (t := ((min t b:ℝ≥0):ℝ)) (sub_pos.mpr (htarget i)) (min t b).2 (Z i).center u]
  rw [show (Z i).target-((min t b:ℝ≥0):ℝ)+((min t b:ℝ≥0):ℝ)=(Z i).target by ring,h₀ i,h₁ i]
  have he := hblock i
  rw [LocalNativeObservations.rows,LocalNativeObservations.rows,
    LocalNativeObservations.stop_observation_process,LocalNativeObservations.stop_observation_process] at he
  rw [show rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ Z b hδ hgap i=
    TwoChannelItoRows.block 𝓕 μ h
      (NativeObservationProcess.process 𝓕 μ h hell₀ hM₀ f₀ hf₀
        (show (b:ℝ)<(Z i).target by have :=hgap i; linarith) (Z i).center)
      (NativeObservationProcess.process 𝓕 μ h hell₁ hM₁ f₁ hf₁
        (show (b:ℝ)<(Z i).target by have :=hgap i; linarith) (Z i).center) by rfl,he]
  ring

theorem predictable_of_representation
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h)
    (R : Fin n → Process (E := Both RealHaarInput) 𝓕 μ h)
    (z : WordRecursion.State n) (U : ℝ≥0 × Ω → RealL2)
    (hc : ∀ ω,Continuous (fun t => U (t,ω)))
    (hRep : ∀ t : ℝ≥0,(fun ω => LocalNativeObservations.stoppedValue δ Z U b (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ h J z R t) :
    StronglyMeasurable[𝓕.predictable] (LocalNativeObservations.stoppedValue δ Z U b) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull
    (fun t ω => LocalNativeObservations.stoppedValue δ Z U b (t,ω))
  · intro t
    obtain ⟨V,hV,he⟩ := StoppedIntegralVersions.vectorIntegral_adapted_version 𝓕 μ h J z R t
    exact ⟨V,hV,(hRep t).trans he⟩
  · intro ω
    exact LocalNativeObservations.stoppedValue_continuous δ Z U b (hc ω)

end SHE.LocalTwoChannelObservations
