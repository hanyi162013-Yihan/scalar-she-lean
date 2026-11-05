module

public import SHE.NativePairScaledMartingale
public import SHE.StoppedInputAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativePairLocalMartingale
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open NativePairScaledMartingale
open scoped NNReal ENNReal
local instance nativePairLocalMartingale_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairLocalMartingale_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairLocalMartingale_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairLocalMartingale_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairLocalMartingale_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairLocalMartingale_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

def value (b : ℝ≥0) (T : ℝ) (x : HeatCircle) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (Λ*((min t b:ℝ≥0):ℝ)) *
    (PositiveGapObservations.coordinate (T-(b:ℝ)) T x (Function.uncurry S.second) (min t b,ω)-
      PositiveGapObservations.coordinate (T-(b:ℝ)) T x (Function.uncurry S.first) (min t b,ω))

theorem continuous_value (b : ℝ≥0) (T : ℝ) (x : HeatCircle) (ω : Ω) :
    Continuous (fun t => value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b T x t ω) := by
  have ht : Continuous (fun t : ℝ≥0 => min t b) := continuous_id.min continuous_const
  have hcU := (PositiveGapObservations.coordinate_continuous (T-(b:ℝ)) T x
    (Function.uncurry S.first) (S.first_continuous ω)).comp ht
  have hcV := (PositiveGapObservations.coordinate_continuous (T-(b:ℝ)) T x
    (Function.uncurry S.second) (S.second_continuous ω)).comp ht
  have he : Continuous (fun t : ℝ≥0 => Real.exp (Λ*((min t b:ℝ≥0):ℝ))) := by fun_prop
  exact he.mul (hcV.sub hcU)

theorem normalized_stopped (hΛ : 0≤Λ) (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    stop 𝓕 μ H (b:ℝ) (normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x)=
      normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x := by
  rw [normalizedInput,StoppedInputAlgebra.stop_weighted,rowDifference,StoppedDampingClock.stop_sub,
    LocalNativeObservations.stop_observation_process,LocalNativeObservations.stop_observation_process]
  simp only [min_self]

theorem normalized_stop (hΛ : 0≤Λ) (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) (t : ℝ≥0) :
    stop 𝓕 μ H (t:ℝ) (normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x)=
      stop 𝓕 μ H ((min t b:ℝ≥0):ℝ)
        (normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x) := by
  calc
    _=stop 𝓕 μ H (t:ℝ) (stop 𝓕 μ H (b:ℝ)
      (normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x)) :=
        congrArg (stop 𝓕 μ H (t:ℝ)) (normalized_stopped 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x).symm
    _=_ := by rw [StoppedInputAlgebra.stop_stop,NNReal.coe_min]

def row (hΛ : 0≤Λ) (b : ℝ≥0) {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) :
    Process (E := RealHaarInput) 𝓕 μ H :=
  Real.exp (Λ*(b:ℝ)) • normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x

include hIJ₀ hIJ₁ in
theorem value_representation (hΛ : 0≤Λ) (b : ℝ≥0) (hbH : b≤H)
    {T : ℝ} (hT : (b:ℝ)<T) (x : HeatCircle) (t : ℝ≥0) :
    value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b T x t=ᵐ[μ]
      fun ω => functional T x (v₀-u₀)+(rightIntegral 𝓕 μ H J).integral
        (stop 𝓕 μ H (t:ℝ) (row 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x)) ω := by
  let N := normalizedInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x
  have he : (rightIntegral 𝓕 μ H J).integral
      (stop 𝓕 μ H (t:ℝ) (row 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x))=
      Real.exp (Λ*(b:ℝ)) • (rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H ((min t b:ℝ≥0):ℝ) N) := by
    rw [row,StoppedInputAlgebra.stop_smul,map_smul,normalized_stop]
  have hc := Lp.coeFn_smul (Real.exp (Λ*(b:ℝ)))
    ((rightIntegral 𝓕 μ H J).integral (stop 𝓕 μ H ((min t b:ℝ≥0):ℝ) N))
  rw [← he] at hc
  filter_upwards [NativePairScaledMartingale.integral_representation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
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
      (Function.uncurry (value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b T x)) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull
  · intro t
    obtain ⟨Z,hZ,hEq⟩ := (rightIntegral 𝓕 μ H J).adapted t
      (stop 𝓕 μ H (t:ℝ) (row 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ b hT x))
      (stop_stopped 𝓕 μ H t _)
    refine ⟨fun ω => functional T x (v₀-u₀)+Z ω,stronglyMeasurable_const.add hZ,?_⟩
    filter_upwards [value_representation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ b hbH hT x t,hEq]
      with ω hω he
    rw [hω,he]
  · exact continuous_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S b T x

end SHE.NativePairLocalMartingale
