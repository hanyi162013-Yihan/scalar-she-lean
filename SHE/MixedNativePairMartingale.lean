module

public import SHE.MixedNativePairConstruction
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativePairScaledMartingale
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
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

def rowDifference (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    Process (E := RealHaarInput) 𝓕 μ H :=
  NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient hT x-
  NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hT x

def normalizedInput (hΛ : 0≤Λ) (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    Process (E := RealHaarInput) 𝓕 μ H :=
  PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ b)
    (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b)
    (rowDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b hT x)

theorem damped_difference_eq (hΛ : 0≤Λ) (b q : ℝ≥0) (hqb : q≤b)
    {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    StoppedInputResolvent.damped 𝓕 μ H
      (rowDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b hT x) hΛ q=
      NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
        (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
        (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
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
          (normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x)) ω := by
  let R := rowDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b hT x
  let N := normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x
  have hTq : (q:ℝ)<T := lt_of_le_of_lt (by exact_mod_cast hqb) hT
  let D := NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q hTq x hΛ
  have he := StoppedDampingClock.integrating_factor 𝓕 μ H hΛ b q hqb R
  rw [damped_difference_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b q hqb hT x] at he
  have heI := congrArg (rightIntegral 𝓕 μ H J).integral he
  rw [map_smul,map_smul] at heI
  change Real.exp (Λ*(q:ℝ)) • (rightIntegral 𝓕 μ H J).integral D=
    Real.exp (Λ*(b:ℝ)) • (rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H (q:ℝ) N) at heI
  filter_upwards [MixedNativePairResolvent.difference_observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hΛ q (hqb.trans hbH) hTq x,
    Lp.coeFn_smul (Real.exp (Λ*(q:ℝ))) ((rightIntegral 𝓕 μ H J).integral D),
    Lp.coeFn_smul (Real.exp (Λ*(b:ℝ))) ((rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H (q:ℝ) N))]
    with ω hd hq hbU
  have hn := congrArg (fun z : Lp ℝ 2 μ => z ω) heI
  rw [hq,hbU] at hn
  change Real.exp (Λ*(q:ℝ))*(rightIntegral 𝓕 μ H J).integral D ω=
    Real.exp (Λ*(b:ℝ))*(rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H (q:ℝ) N) ω at hn
  rw [hd]
  have hexp : Real.exp (Λ*(q:ℝ))*Real.exp (-Λ*(q:ℝ))=1 := by
    rw [← Real.exp_add,show Λ*(q:ℝ)+ -Λ*(q:ℝ)=0 by ring,Real.exp_zero]
  change Real.exp (Λ*(q:ℝ))*(Real.exp (-Λ*(q:ℝ))*functional T x (v₀-u₀)+
    (rightIntegral 𝓕 μ H J).integral D ω)=_
  rw [mul_add,← mul_assoc,hexp,one_mul,hn]

end SHE.MixedNativePairScaledMartingale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.MixedNativePairLocalMartingale
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open MixedNativePairScaledMartingale
open scoped NNReal ENNReal
local instance nativePairLocalMartingale_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairLocalMartingale_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairLocalMartingale_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairLocalMartingale_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairLocalMartingale_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairLocalMartingale_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

def value (b : ℝ≥0) (T : ℝ) (x : HeatCircle) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (Λ*((min t b:ℝ≥0):ℝ)) *
    (PositiveGapObservations.coordinate (T-(b:ℝ)) T x (Function.uncurry S.second) (min t b,ω)-
      PositiveGapObservations.coordinate (T-(b:ℝ)) T x (Function.uncurry S.first) (min t b,ω))

theorem continuous_value (b : ℝ≥0) (T : ℝ) (x : HeatCircle) (ω : Ω) :
    Continuous (fun t => value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b T x t ω) := by
  have ht : Continuous (fun t : ℝ≥0 => min t b) := continuous_id.min continuous_const
  have hcU := (PositiveGapObservations.coordinate_continuous (T-(b:ℝ)) T x
    (Function.uncurry S.first) (S.first_continuous ω)).comp ht
  have hcV := (PositiveGapObservations.coordinate_continuous (T-(b:ℝ)) T x
    (Function.uncurry S.second) (S.second_continuous ω)).comp ht
  have he : Continuous (fun t : ℝ≥0 => Real.exp (Λ*((min t b:ℝ≥0):ℝ))) := by fun_prop
  exact he.mul (hcV.sub hcU)

theorem normalized_stopped (hΛ : 0≤Λ) (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    stop 𝓕 μ H (b:ℝ) (normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x)=
      normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x := by
  rw [normalizedInput,StoppedInputAlgebra.stop_weighted,rowDifference,StoppedDampingClock.stop_sub,
    LocalNativeObservations.stop_observation_process,LocalNativeObservations.stop_observation_process]
  simp only [min_self]

theorem normalized_stop (hΛ : 0≤Λ) (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) (t : ℝ≥0) :
    stop 𝓕 μ H (t:ℝ) (normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x)=
      stop 𝓕 μ H ((min t b:ℝ≥0):ℝ)
        (normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x) := by
  calc
    _=stop 𝓕 μ H (t:ℝ) (stop 𝓕 μ H (b:ℝ)
      (normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x)) :=
        congrArg (stop 𝓕 μ H (t:ℝ)) (normalized_stopped 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x).symm
    _=_ := by rw [StoppedInputAlgebra.stop_stop,NNReal.coe_min]

def row (hΛ : 0≤Λ) (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    Process (E := RealHaarInput) 𝓕 μ H :=
  Real.exp (Λ*(b:ℝ)) • normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x

include hIJ₀ hIJ₁ in
theorem value_representation (hΛ : 0≤Λ) (b : ℝ≥0) (hbH : b≤H)
    {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) (t : ℝ≥0) :
    value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b T x t=ᵐ[μ]
      fun ω => functional T x (v₀-u₀)+(rightIntegral 𝓕 μ H J).integral
        (stop 𝓕 μ H (t:ℝ) (row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x)) ω := by
  let N := normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x
  have he : (rightIntegral 𝓕 μ H J).integral
      (stop 𝓕 μ H (t:ℝ) (row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x))=
      Real.exp (Λ*(b:ℝ)) • (rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H ((min t b:ℝ≥0):ℝ) N) := by
    rw [row,StoppedInputAlgebra.stop_smul,map_smul,normalized_stop]
  have hc := Lp.coeFn_smul (Real.exp (Λ*(b:ℝ)))
    ((rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H ((min t b:ℝ≥0):ℝ) N))
  rw [← he] at hc
  filter_upwards [MixedNativePairScaledMartingale.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ b hbH hT x (min t b) (min_le_right t b),hc] with ω hω hc
  have hg : T-(b:ℝ)≤T-((min t b:ℝ≥0):ℝ) := sub_le_sub_left (by exact_mod_cast min_le_right t b) T
  change Real.exp (Λ*((min t b:ℝ≥0):ℝ)) *
    (PositiveGapObservations.coordinate (T-(b:ℝ)) T x (Function.uncurry S.second) (min t b,ω)-
      PositiveGapObservations.coordinate (T-(b:ℝ)) T x (Function.uncurry S.first) (min t b,ω))=_
  rw [PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr hT) _ _ _ hg,
    PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr hT) _ _ _ hg,← map_sub]
  change Real.exp (Λ*((min t b:ℝ≥0):ℝ))*functional (T-((min t b:ℝ≥0):ℝ)) x
    (S.second (min t b) ω-S.first (min t b) ω)=_
  rw [hω,hc]
  rfl

include hIJ₀ hIJ₁ in
theorem predictable_value (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hΛ : 0≤Λ) (b : ℝ≥0) (hbH : b≤H) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b T x)) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull
  · intro t
    obtain ⟨Z,hZ,hEq⟩ := (rightIntegral 𝓕 μ H J).adapted t
      (stop 𝓕 μ H (t:ℝ) (row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b hT x))
      (stop_stopped 𝓕 μ H t _)
    refine ⟨fun ω => functional T x (v₀-u₀)+Z ω,stronglyMeasurable_const.add hZ,?_⟩
    filter_upwards [value_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ b hbH hT x t,hEq]
      with ω hω he
    rw [hω,he]
  · exact continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b T x

end SHE.MixedNativePairLocalMartingale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace SHE.MixedNativePairExtendedMartingale
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
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable {n : ℕ} (target : Fin n→ℝ) (centers : Fin n→HeatCircle) (b : ℝ≥0)
variable (hgap : ∀ i,(b:ℝ)<target i)

def value (t : ℝ≥0) (ω : Ω) : WordRecursion.State (n+n) :=
  WithLp.toLp 2 (Fin.append
    (fun i => PositiveGapObservations.coordinate (target i-(b:ℝ)) (target i) (centers i)
      (Function.uncurry S.first) (min t b,ω))
    (fun i => MixedNativePairLocalMartingale.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b (target i) (centers i) t ω))

def initial : WordRecursion.State (n+n) :=
  WithLp.toLp 2 (Fin.append (fun i => functional (target i) (centers i) u₀)
    (fun i => functional (target i) (centers i) (v₀-u₀)))

def rows (hΛ : 0≤Λ) : Fin (n+n)→Process (E := Both RealHaarInput) 𝓕 μ H :=
  Fin.append
    (fun i => MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b (hgap i) (centers i))
    (fun i => NativeHybridInput.rightLift 𝓕 μ H
      (MixedNativePairLocalMartingale.row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ b (hgap i) (centers i)))

theorem continuous_value (ω : Ω) :
    Continuous (fun t => value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S target centers b t ω) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+n) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have ht : Continuous (fun t : ℝ≥0 => min t b) := continuous_id.min continuous_const
    simpa only [Fin.append_left,Function.comp_def] using
      (PositiveGapObservations.coordinate_continuous (target j-(b:ℝ)) (target j) (centers j)
        (Function.uncurry S.first) (S.first_continuous ω)).comp ht
  · simpa only [Fin.append_right] using MixedNativePairLocalMartingale.continuous_value
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b (target j) (centers j) ω

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
    value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S target centers b t=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (initial u₀ v₀ target centers)
        (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S target centers b hgap hΛ) t := by
  have hU (i : Fin n) :
      (fun ω => PositiveGapObservations.coordinate (target i-(b:ℝ)) (target i) (centers i)
        (Function.uncurry S.first) (min t b,ω))=ᵐ[μ]
      fun ω => functional (target i) (centers i) u₀+J.integral
        (stop 𝓕 μ H (t:ℝ)
          (MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b (hgap i) (centers i))) ω := by
    have hT : ((min t b:ℝ≥0):ℝ)<target i :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right t b) (hgap i)
    have hs : stop 𝓕 μ H (t:ℝ)
        (MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b (hgap i) (centers i))=
      MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (min t b) hT (centers i) := by
      rw [MixedNativePairObservedFirst.rows,TwoChannelItoRows.stop_block,
        LocalNativeObservations.stop_observation_process,LocalNativeObservations.stop_observation_process]
      rfl
    filter_upwards [MixedNativePairObservedFirst.observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      (min t b) ((min_le_right t b).trans hbH) hT (centers i)] with ω hω
    rw [PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _
      (sub_le_sub_left (by exact_mod_cast min_le_right t b) (target i)),hs]
    exact hω
  have hD (i : Fin n) := MixedNativePairLocalMartingale.value_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
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
      (Function.uncurry (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S target centers b)) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull
  · intro t
    obtain ⟨V,hV,he⟩ := StoppedIntegralVersions.vectorIntegral_adapted_version 𝓕 μ H J
      (initial u₀ v₀ target centers) (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S target centers b hgap hΛ) t
    exact ⟨V,hV,(integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      target centers b hgap hΛ hbH t).trans he⟩
  · exact continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S target centers b

end SHE.MixedNativePairExtendedMartingale
