module

public import SHE.NativeJointObservations
public import SHE.NativePairHybridMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.NativeJointMoments
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativeJointMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b q : ℝ≥0)

def displacement (i : Fin n) (ω : Ω) : ℝ :=
  NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q ω i-
    NativeJointObservations.initial Λ u₀ v₀ Z i

/-- The printed joint mean uses its original stop sigma, not the heat
target T. Its centered actual observation is exactly the honest hybrid
current displacement with theta=exp(-Lambda(sigma-q)). -/
theorem displacement_eq_hybrid (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b) (i : Fin n) (ω : Ω) :
    displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q i ω=
      NativePairHybridMoments.displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
        q (Z i).target (Z i).center (Real.exp (-Λ*((Z i).stop-(q:ℝ)))) ω := by
  rw [displacement,NativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap q hqb ω i,
    NativeJointObservations.initial_apply]
  unfold NativePairHybridMoments.displacement
  rw [map_add,map_smul]
  have he : Real.exp (-Λ*((Z i).stop-(q:ℝ)))*Real.exp (-Λ*(q:ℝ))=Real.exp (-Λ*(Z i).stop) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change _=_+Real.exp (-Λ*((Z i).stop-(q:ℝ)))*_-
    (_+Real.exp (-Λ*((Z i).stop-(q:ℝ)))*Real.exp (-Λ*(q:ℝ))*_)
  rw [he]

theorem weight_bound (hΛ : 0≤Λ) (i : Fin n) (hstop : (q:ℝ)≤(Z i).stop) :
    |Real.exp (-Λ*((Z i).stop-(q:ℝ)))|≤1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (sub_nonneg.mpr hstop)

include hIJ₀ hIJ₁ in
/-- All-even moments of actual drift-cancelling joint observations
around their literal printed mean, uniformly over future original stops
and arbitrary further heat targets. No Gaussian current-state premise. -/
theorem moment (hΛ : 0≤Λ) (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b)
    (hqH : q≤H) (hq1 : (q:ℝ)≤1) (i : Fin n) (hstop : (q:ℝ)≤(Z i).stop)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    (∫⁻ ω,ENNReal.ofReal (‖displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q i ω‖^(2*p)) ∂μ)≤
      ENNReal.ofReal (NativeHybridMoments.momentConstant p B κ M*(q:ℝ)^((p:ℝ)/2)) := by
  have hqT : (q:ℝ)<(Z i).target := lt_of_le_of_lt (by exact_mod_cast hqb) (hgap i)
  have hh := NativePairHybridMoments.moment 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hΛ q hqH hq1 hqT (Z i).center (weight_bound Λ Z q hΛ i hstop) p B hBDG
  simpa only [displacement_eq_hybrid 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q hgap hqb i] using hh

include hIJ₀ hIJ₁ in
theorem fractional_moment (hΛ : 0≤Λ) (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b)
    (hqH : q≤H) (hq1 : (q:ℝ)≤1) (i : Fin n) (hstop : (q:ℝ)≤(Z i).stop)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω => |displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q i ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q i ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  have hqT : (q:ℝ)<(Z i).target := lt_of_le_of_lt (by exact_mod_cast hqb) (hgap i)
  have hh := NativePairHybridMoments.fractional_moment 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hΛ q hqH hq1 hqT (Z i).center (weight_bound Λ Z q hΛ i hstop) p B hBDG hβ hβ1
  simpa only [displacement_eq_hybrid 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q hgap hqb i] using hh

end SHE.NativeJointMoments
