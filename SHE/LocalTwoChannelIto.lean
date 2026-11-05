module

public import SHE.LocalTwoChannelObservations
public import SHE.LocalNativeItoBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.LocalTwoChannelIto
open MeasureTheory Set PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
open NativeHeatObservation NativeObservationNaturality WordRecursion OrthogonalItoChannels
open scoped NNReal ENNReal
local instance localTwoChannelIto_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance localTwoChannelIto_realSigma : MeasurableSpace RealL2 := borel _
local instance localTwoChannelIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance localTwoChannelIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance localTwoChannelIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance localTwoChannelIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance localTwoChannelIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell₀ M₀ ell₁ M₁ : ℝ} (hell₀ : 0 < ell₀) (hM₀ : 0 ≤ M₀)
variable (f₀ : ℝ≥0 × Ω → EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell₁ : 0 < ell₁) (hM₁ : 0 ≤ M₁)
variable (f₁ : ℝ≥0 × Ω → EllipticField ell₁ M₁) (hf₁ : StronglyMeasurable[𝓕.predictable] f₁)
variable {n : ℕ} (Z : Fin n → Observation) (b : ℝ≥0)
variable {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(b:ℝ))

theorem rowCovariance_eq_sum (hb : b ≤ h) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (b:ℝ)),
      StandardFiniteIto.rowCovariance 𝓕 μ h
        (LocalTwoChannelObservations.rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ Z b hδ hgap) ω t=
      CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f₀ ω) Z t+
        CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f₁ ω) Z t := by
  have hsum := TwoChannelItoRows.rowCovariance_sum_ae_real 𝓕 μ h
    (LocalNativeObservations.rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ Z b hδ hgap)
    (LocalNativeObservations.rows 𝓕 μ h hell₁ hM₁ f₁ hf₁ Z b hδ hgap)
  filter_upwards [hsum,LocalNativeItoBracket.rowCovariance_eq_density 𝓕 μ h hell₀ hM₀ f₀ hf₀ Z b hδ hgap hb,
    LocalNativeItoBracket.rowCovariance_eq_density 𝓕 μ h hell₁ hM₁ f₁ hf₁ Z b hδ hgap hb] with ω hsum h₀ h₁
  have hs : Ioc (0:ℝ) (b:ℝ) ⊆ Ioc (0:ℝ) (h:ℝ) := by
    intro t ht
    exact ⟨ht.1,ht.2.trans (by exact_mod_cast hb)⟩
  filter_upwards [hsum.filter_mono (ae_mono (Measure.restrict_mono_set volume hs)),h₀,h₁] with t hsum h₀ h₁
  exact hsum.trans (congrArg₂ (·+·) h₀ h₁)

theorem finiteItoInput_of_sum_density (hb : b ≤ h) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ (b:ℝ))
    (Y : Ω → ℝ → WordRecursion.State n) (N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ)
    (hi : PhysicalIto.FiniteItoInput μ Y
      (StandardFiniteIto.rowCovariance 𝓕 μ h
        (LocalTwoChannelObservations.rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ Z b hδ hgap)) a b N) :
    PhysicalIto.FiniteItoInput μ Y
      (fun ω t => CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f₀ ω) Z t+
        CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f₁ ω) Z t) a b N := by
  intro G dG hG
  filter_upwards [hi G dG hG,rowCovariance_eq_sum 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ Z b hδ hgap hb]
    with ω hω hΓ
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  have hs : Ioc a (b:ℝ) ⊆ Ioc (0:ℝ) (b:ℝ) := fun t ht => ⟨ha.trans_lt ht.1,ht.2⟩
  filter_upwards [hΓ.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))] with t ht
  rw [ht]

include hM₀ hf₀ hM₁ hf₁ hδ hgap in
/-- Actual local physical Itô input for two common channels. The exact
bracket is their sum; neither channel is replaced by a total Haar factor. -/
theorem finiteItoInput
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ h J))
    (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ h J))
    (hJ : StandardFiniteIto.Universal 𝓕 μ h J)
    (u : RealL2) (U : ℝ≥0 × Ω → RealL2) (hc : ∀ ω,Continuous (fun t => U (t,ω)))
    (v₀ v₁ : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv₀ : ∀ t : ℝ≥0,t ≤ h → v₀ t=ᵐ[energyMeasure μ h]
      (fun p => kernel ell₀ M₀ hell₀ ((t:ℝ)-(p.1:ℝ),f₀ p)))
    (hv₁ : ∀ t : ℝ≥0,t ≤ h → v₁ t=ᵐ[energyMeasure μ h]
      (fun p => kernel ell₁ M₁ hell₁ ((t:ℝ)-(p.1:ℝ),f₁ p)))
    (hmild : ∀ t : ℝ≥0,t ≤ h → ∀ᵐ ω ∂μ,U (t,ω)=
      NativeHeatObservation.heat (t:ℝ) u+I₀.integral (v₀ t) ω+I₁.integral (v₁ t) ω)
    (hb : b ≤ h) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ (b:ℝ)) (X : Ω → ℝ × HeatCircle → ℝ) :
    ∃ N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ,
      (∀ G,Integrable (N G) μ ∧ (∫ ω,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ
        (fun ω => observe (fun r => embed (U (r.toNNReal,ω))) (X ω) Z)
        (fun ω t => CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f₀ ω) Z t+
          CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f₁ ω) Z t) a b N := by
  let Y := LocalNativeObservations.stoppedValue δ Z U b
  let R := LocalTwoChannelObservations.rows 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ Z b hδ hgap
  have hRep := LocalTwoChannelObservations.integral_representation 𝓕 μ h hell₀ hM₀ f₀ hf₀
    hell₁ hM₁ f₁ hf₁ Z b hδ hgap I₀ I₁ J hIJ₀ hIJ₁ u U v₀ v₁ hv₀ hv₁ hmild hb
  have hY := LocalTwoChannelObservations.predictable_of_representation
    (δ := δ) 𝓕 μ h Z b hnull J R (PositiveGapObservations.initial Z u) U hc hRep
  let N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ := fun G ω =>
    FiniteItoNoise.noise 𝓕 μ h Y hY R J a b G ω
  have hi := StandardFiniteIto.finiteItoInput 𝓕 μ h J hJ R (PositiveGapObservations.initial Z u) Y hY
    (fun ω => LocalNativeObservations.stoppedValue_continuous δ Z U b (hc ω))
    (fun t _ => hRep t) ha hab (by exact_mod_cast hb)
  have hd := finiteItoInput_of_sum_density 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ Z b hδ hgap hb ha hab _ N hi
  have hp := NativeObservationIto.finiteItoInput_congr_path μ hab hd
    (fun ω t ht => LocalNativeObservationIto.stoppedValue_eq_observe (Z := Z) (b := b) (hδ := hδ) (hgap := hgap)
      U X ω (ha.trans ht.1) ht.2)
  refine ⟨N,fun G => ⟨?_,?_⟩,hp⟩
  · exact FiniteItoNoise.noise_integrable 𝓕 μ h Y hY R J a b G
  · exact FiniteItoNoise.noise_centered 𝓕 μ h Y hY R J a b G

end SHE.LocalTwoChannelIto
