module

public import SHE.FiniteReferenceSplice
public import SHE.FiniteItoPastNoise

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.FiniteReferenceSplice
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {n : ℕ} (v : ℝ≥0) (R S : Fin n → Process (E:=C) 𝓕 μ H)
variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) (z : WordRecursion.State n)
variable (K L : Fin n→ℝ) (hK : ∀ i,0≤K i) (hL : ∀ i,0≤L i)
variable (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖R i p‖^2≤K i)
variable (hS : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖S i p‖^2≤L i)

def jointCap : Fin (n+n)→ℝ := Fin.append K (fun i => K i+L i)

include hK hL in
theorem jointCap_nonneg : ∀ i,0≤jointCap K L i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [jointCap,Fin.append_left] using hK j
  · simpa only [jointCap,Fin.append_right] using add_nonneg (hK j) (hL j)

include hK hL hR hS in
theorem jointRows_bound : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖jointRows 𝓕 μ H v R S i p‖^2≤jointCap K L i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [jointRows,jointCap,Fin.append_left] using hR j
  · simpa only [jointRows,jointCap,Fin.append_right] using rows_bound 𝓕 μ H v R S K L hK hL hR hS j

variable (hH : (H:ℝ)≤1) (hH0 : 0<H)
variable (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)

include K L hK hL hR hS hH hH0 B hBDG in
theorem integral_representation (t : ℝ≥0) (ht : t≤H) :
    (fun ω => value 𝓕 μ H v R S J z (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (jointInitial z) (jointRows 𝓕 μ H v R S) t :=
  BoundedVectorIntegral.integral_representation 𝓕 μ H J (jointInitial z) (jointRows 𝓕 μ H v R S)
    hH hH0 B hBDG (jointCap K L) (jointCap_nonneg K L hK hL)
    (jointRows_bound 𝓕 μ H v R S K L hK hL hR hS) t ht

include K L hK hL hR hS hH hH0 B hBDG in
theorem predictable_value (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ) :
    StronglyMeasurable[𝓕.predictable] (value 𝓕 μ H v R S J z) :=
  BoundedVectorIntegral.predictable_value 𝓕 μ H J (jointInitial z) (jointRows 𝓕 μ H v R S)
    hH hH0 hnull B hBDG (jointCap K L) (jointCap_nonneg K L hK hL)
    (jointRows_bound 𝓕 μ H v R S K L hK hL hR hS)

include K L hK hL hR hS hH hH0 B hBDG in
/-- The actual two-coordinate comparison retains centering on EVERY
original past event. The martingale is the true common-J gradient integral. -/
theorem finiteItoInput_on_past_event (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J)
    (c : ℝ≥0) (hvc : v≤c) (hcH : c≤H) :
    ∃ N : (ℝ→WordRecursion.State (n+n)→ℝ)→Ω→ℝ,
      (∀ G,Integrable (N G) μ ∧ ∀ A,MeasurableSet[𝓕 v] A → (∫ ω in A,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ (fun ω t => value 𝓕 μ H v R S J z (t.toNNReal,ω))
        (StandardFiniteIto.rowCovariance 𝓕 μ H (jointRows 𝓕 μ H v R S)) v c N := by
  let Y := value 𝓕 μ H v R S J z
  have hY := predictable_value 𝓕 μ H v R S J z K L hK hL hR hS hH hH0 B hBDG hnull
  let N := fun G ω => FiniteItoNoise.noise 𝓕 μ H Y hY (jointRows 𝓕 μ H v R S) J v c G ω
  refine ⟨N,fun G => ⟨FiniteItoNoise.noise_integrable 𝓕 μ H Y hY _ J v c G,
    fun A hA => FiniteItoPastNoise.noise_centered_on_past_event 𝓕 μ H Y hY _ J hlocal v c hvc G A hA⟩,?_⟩
  exact StandardFiniteIto.finiteItoInput 𝓕 μ H J hJ (jointRows 𝓕 μ H v R S) (jointInitial z)
    Y hY (BoundedVectorIntegral.continuous_value 𝓕 μ H J (jointInitial z) _ hH0)
    (integral_representation 𝓕 μ H v R S J z K L hK hL hR hS hH hH0 B hBDG)
    v.2 (by exact_mod_cast hvc) (by exact_mod_cast hcH)

end SHE.FiniteReferenceSplice
