module

public import SHE.MixedNativePairMartingale
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativePastIncrement
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativePastIncrement_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativePastIncrement_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativePastIncrement_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativePastIncrement_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativePastIncrement_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativePastIncrement_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

open PastItoInputs PastItoAlgebra
local notation "Rows" => MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "N" => MixedNativePairScaledMartingale.normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

theorem post_rows_eq (v q : ℝ≥0) (hvq : v≤q) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    post 𝓕 μ H v (Rows q hT x)=Rows q hT x-Rows v (lt_of_le_of_lt (by exact_mod_cast hvq) hT) x := by
  have hs := MixedNativePairObservedFirst.stop_rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q q le_rfl hT x
  have he := post_stop_eq_sub 𝓕 μ H v q hvq (Rows q hT x)
  rw [hs,MixedNativePairObservedFirst.stop_rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q v hvq hT x] at he
  exact he

include hIJ₀ hIJ₁ in
/-- Literal observed mild increment after an arbitrary past time. The
random past state is the actual U_v, and the integral is the original J. -/
theorem first_increment (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) :
    (fun ω => functional (T-(q:ℝ)) x (S.first q ω)-functional (T-(v:ℝ)) x (S.first v ω))=ᵐ[μ]
      J.integral (post 𝓕 μ H v (Rows q hT x)) := by
  have he := congrArg J.integral (post_rows_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v q hvq hT x)
  rw [map_sub] at he
  filter_upwards [MixedNativePairObservedFirst.observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ q hqH hT x,
    MixedNativePairObservedFirst.observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ v (hvq.trans hqH)
      (lt_of_le_of_lt (by exact_mod_cast hvq) hT) x,
    Lp.coeFn_sub (J.integral (Rows q hT x))
      (J.integral (Rows v (lt_of_le_of_lt (by exact_mod_cast hvq) hT) x))] with ω hq hv hs
  have hi := congrArg (fun z : Lp ℝ 2 μ => z ω) he
  rw [hs] at hi
  simp only [Pi.sub_apply] at hi
  rw [hq,hv,hi]
  ring

include hIJ₀ hIJ₁ in
/-- The actual controlled difference over [v,q] is centered at the
random D_v and integrated by the same residual channel of full-H J. -/
theorem difference_increment (hΛ : 0≤Λ) (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) :
    (fun ω => functional (T-(q:ℝ)) x (S.second q ω-S.first q ω)-
      Real.exp (-Λ*((q:ℝ)-(v:ℝ)))*functional (T-(v:ℝ)) x (S.second v ω-S.first v ω))=ᵐ[μ]
      (rightIntegral 𝓕 μ H J).integral (post 𝓕 μ H v (N hΛ q hT x)) := by
  let I := rightIntegral 𝓕 μ H J
  let u := N hΛ q hT x
  have hstop : stop 𝓕 μ H (q:ℝ) u=u :=
    MixedNativePairLocalMartingale.normalized_stopped 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ q hT x
  have he := post_stop_eq_sub 𝓕 μ H v q hvq u
  rw [hstop] at he
  have heI := congrArg I.integral he
  rw [map_sub] at heI
  have hq := MixedNativePairScaledMartingale.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hΛ q hqH hT x q le_rfl
  have hv := MixedNativePairScaledMartingale.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hΛ q hqH hT x v hvq
  change (fun ω => Real.exp (Λ*(q:ℝ))*functional (T-(q:ℝ)) x (S.second q ω-S.first q ω))=ᵐ[μ]
    (fun ω => functional T x (v₀-u₀)+Real.exp (Λ*(q:ℝ))*I.integral (stop 𝓕 μ H (q:ℝ) u) ω) at hq
  rw [hstop] at hq
  change (fun ω => Real.exp (Λ*(v:ℝ))*functional (T-(v:ℝ)) x (S.second v ω-S.first v ω))=ᵐ[μ]
    (fun ω => functional T x (v₀-u₀)+Real.exp (Λ*(q:ℝ))*I.integral (stop 𝓕 μ H (v:ℝ) u) ω) at hv
  filter_upwards [hq,hv,Lp.coeFn_sub (I.integral u) (I.integral (stop 𝓕 μ H (v:ℝ) u))] with ω hq hv hs
  have hi := congrArg (fun z : Lp ℝ 2 μ => z ω) heI
  rw [hs] at hi
  simp only [Pi.sub_apply] at hi
  apply mul_left_cancel₀ (Real.exp_ne_zero (Λ*(q:ℝ)))
  have hexp : Real.exp (Λ*(q:ℝ))*Real.exp (-Λ*((q:ℝ)-(v:ℝ)))=Real.exp (Λ*(v:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (Λ*(q:ℝ))*functional (T-(q:ℝ)) x (S.second q ω-S.first q ω)-
        Real.exp (Λ*(v:ℝ))*functional (T-(v:ℝ)) x (S.second v ω-S.first v ω) := by rw [mul_sub,← mul_assoc,hexp]
    _ = Real.exp (Λ*(q:ℝ))*(I.integral u ω-I.integral (stop 𝓕 μ H (v:ℝ) u) ω) := by rw [hq,hv]; ring
    _ = _ := by rw [hi]

end SHE.MixedNativePastIncrement
