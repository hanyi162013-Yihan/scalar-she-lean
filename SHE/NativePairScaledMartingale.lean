module

public import SHE.NativePairResolvent
public import SHE.StoppedDampingClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativePairScaledMartingale
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance nativePairScaledMartingale_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairScaledMartingale_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairScaledMartingale_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairScaledMartingale_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairScaledMartingale_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairScaledMartingale_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

def rowDifference (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    Process (E := RealHaarInput) 𝓕 μ H :=
  NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second) S.second_coefficient hT x-
  NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient hT x

def normalizedInput (hΛ : 0≤Λ) (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    Process (E := RealHaarInput) 𝓕 μ H :=
  PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ b)
    (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b)
    (rowDifference 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b hT x)

theorem damped_difference_eq (hΛ : 0≤Λ) (b q : ℝ≥0) (hqb : q≤b)
    {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    StoppedInputResolvent.damped 𝓕 μ H
      (rowDifference 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b hT x) hΛ q=
      NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
        (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
        (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
        S.first_coefficient S.second_coefficient q
        (lt_of_le_of_lt (by exact_mod_cast hqb) hT) x hΛ := by
  rw [StoppedInputResolvent.damped,rowDifference,StoppedDampingClock.stop_sub,
    LocalNativeObservations.stop_observation_process,LocalNativeObservations.stop_observation_process]
  simp only [min_eq_left hqb]
  rfl

include hIJ₀ hIJ₁ in
/-- The exponentially rescaled actual observed difference is an ordinary
stopped martingale with one fixed predictable input on the full horizon.
All q≤b use that same input and that same residual noise integral. -/
theorem integral_representation (hΛ : 0≤Λ) (b : ℝ≥0) (hbH : b≤H)
    {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) (q : ℝ≥0) (hqb : q≤b) :
    (fun ω => Real.exp (Λ*(q:ℝ))*functional (T-(q:ℝ)) x (S.second q ω-S.first q ω))=ᵐ[μ]
      fun ω => functional T x (v₀-u₀)+Real.exp (Λ*(b:ℝ))*
        (rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H (q:ℝ)
          (normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x)) ω := by
  let R := rowDifference 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b hT x
  let N := normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x
  have hTq : (q:ℝ)<T := lt_of_le_of_lt (by exact_mod_cast hqb) hT
  let D := NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    S.first_coefficient S.second_coefficient q hTq x hΛ
  have he := StoppedDampingClock.integrating_factor 𝓕 μ H hΛ b q hqb R
  rw [damped_difference_eq 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b q hqb hT x] at he
  have heI := congrArg (rightIntegral 𝓕 μ H J).integral he
  rw [map_smul,map_smul] at heI
  change Real.exp (Λ*(q:ℝ)) • (rightIntegral 𝓕 μ H J).integral D=
    Real.exp (Λ*(b:ℝ)) • (rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H (q:ℝ) N) at heI
  filter_upwards [NativePairResolvent.difference_observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hΛ q (hqb.trans hbH) hTq x,
    Lp.coeFn_smul (Real.exp (Λ*(q:ℝ))) ((rightIntegral 𝓕 μ H J).integral D),
    Lp.coeFn_smul (Real.exp (Λ*(b:ℝ))) ((rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H (q:ℝ) N))]
    with ω hd hq hb
  have hn := congrArg (fun z : Lp ℝ 2 μ => z ω) heI
  rw [hq,hb] at hn
  change Real.exp (Λ*(q:ℝ))*(rightIntegral 𝓕 μ H J).integral D ω=
    Real.exp (Λ*(b:ℝ))*(rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H (q:ℝ) N) ω at hn
  rw [hd]
  have hexp : Real.exp (Λ*(q:ℝ))*Real.exp (-Λ*(q:ℝ))=1 := by
    rw [← Real.exp_add,show Λ*(q:ℝ)+ -Λ*(q:ℝ)=0 by ring,Real.exp_zero]
  change Real.exp (Λ*(q:ℝ))*(Real.exp (-Λ*(q:ℝ))*functional T x (v₀-u₀)+
    (rightIntegral 𝓕 μ H J).integral D ω)=_
  rw [mul_add,← mul_assoc,hexp,one_mul,hn]

end SHE.NativePairScaledMartingale
