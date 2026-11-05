module
public import SHE.OriginalNativeHeatEquation
public import SHE.PastItoAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.OriginalNativePastIncrement
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle PredictableL2
open OrthogonalItoChannels StoppedFourier NativeHeatObservation PredictableScalarHaarRotation
open scoped NNReal ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (D : SmoothApproximation.ScalarData)
variable (B : StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H) (u₀ : RealL2)
variable (S : OriginalNativeHeatEquation.Data 𝓕 μ H D B u₀)

theorem stop_row {T q : ℝ} (hq : q<T) (v : ℝ) (hvq : v≤q) (x : HeatCircle) :
    StoppedItoInputs.stop 𝓕 μ H v
      (originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable hq x)=
      originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable (hvq.trans_lt hq) x := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [StoppedItoInputs.stop_ae 𝓕 μ H v
      (originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable hq x),
    originalRow_ae 𝓕 μ H D (Function.uncurry S.value) S.predictable hq x,
    originalRow_ae 𝓕 μ H D (Function.uncurry S.value) S.predictable (hvq.trans_lt hq) x] with p hs hqrow hvrow
  rw [hs,hvrow]
  by_cases hp : (p.1:ℝ)<v
  · rw [Set.indicator_of_mem (show p∈StoppedItoInputs.before (Ω:=Ω) v from hp),hqrow,
      ite_eq_left (hp.trans_le hvq),ite_eq_left hp]
  · rw [Set.indicator_of_notMem (show p∉StoppedItoInputs.before (Ω:=Ω) v from hp),ite_eq_right hp]

/-- The original one-noise observable equation restarts at its actual
random past state. This is proved for arbitrary horizons before any
conditional-law or SPDE restart construction is attempted. -/
theorem increment (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) :
    (fun ω => functional (T-(q:ℝ)) x (S.value q ω)-
      functional (T-(v:ℝ)) x (S.value v ω))=ᵐ[μ]
      B.integral (PastItoInputs.post 𝓕 μ H v
        (originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable hT x)) := by
  have hvqr : (v:ℝ)≤q := by exact_mod_cast hvq
  have hvT : (v:ℝ)<T := hvqr.trans_lt hT
  have he := PastItoAlgebra.post_stop_eq_sub 𝓕 μ H v q hvq
    (originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable hT x)
  rw [stop_row 𝓕 μ H D B u₀ S hT (q:ℝ) le_rfl x,
    stop_row 𝓕 μ H D B u₀ S hT (v:ℝ) hvqr x] at he
  have hei := congrArg B.integral he
  rw [map_sub] at hei
  have eqQ := S.equation q hqH (T-(q:ℝ)) (sub_pos.mpr hT) x
  have eqV := S.equation v (hvq.trans hqH) (T-(v:ℝ)) (sub_pos.mpr hvT) x
  have hqTarget : (q:ℝ)+(T-(q:ℝ))=T := by ring
  have hvTarget : (v:ℝ)+(T-(v:ℝ))=T := by ring
  simp only [hqTarget] at eqQ
  simp only [hvTarget] at eqV
  filter_upwards [eqQ,eqV,Lp.coeFn_sub
    (B.integral (originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable hT x))
    (B.integral (originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable hvT x))] with ω hq hv hs
  have hi := congrArg (fun z : Lp ℝ 2 μ => z ω) hei
  rw [hs] at hi
  simp only [Pi.sub_apply] at hi
  rw [hq,hv,hi]
  ring

/-- The deterministic semigroup term in the restarted observable mild
equation is exactly heat(q) of the actual random state U(v). -/
theorem restart_observation (v q : ℝ≥0) (hvqH : v+q≤H)
    (ε : ℝ) (hε : 0<ε) (x : HeatCircle) :
    (fun ω => functional ε x (S.value (v+q) ω))=ᵐ[μ]
      (fun ω => functional ε x (heat (q:ℝ) (S.value v ω))+
        B.integral (PastItoInputs.post 𝓕 μ H v
          (originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable
            (T:=((v+q:ℝ≥0):ℝ)+ε) (t:=((v+q:ℝ≥0):ℝ)) (by linarith) x)) ω) := by
  have hvle : v≤v+q := le_add_of_nonneg_right q.2
  have he := increment 𝓕 μ H D B u₀ S v (v+q) hvle hvqH
    (T:=((v+q:ℝ≥0):ℝ)+ε) (by linarith) x
  have h1 : (((v+q:ℝ≥0):ℝ)+ε)-((v+q:ℝ≥0):ℝ)=ε := by ring
  have h2 : (((v+q:ℝ≥0):ℝ)+ε)-(v:ℝ)=ε+(q:ℝ) := by push_cast;ring
  filter_upwards [he] with ω hω
  simp only [h1,h2] at hω
  have hh := NativeHeatObservation.functional_heat hε q.2 x (S.value v ω)
  apply sub_eq_iff_eq_add'.mp
  convert hω using 1
  exact congrArg (fun r : ℝ => functional ε x (S.value (v+q) ω)-r) hh

/-- The observed model has the actual prescribed initial state. -/
theorem initial : S.value 0=ᵐ[μ] fun _=>u₀ := by
  apply HeatObservationUniqueness.ae_eq μ (S.value 0) (fun _=>u₀)
    (((S.predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)) measurable_const
  intro ε hε x
  have hr : originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable
      (T:=ε) (t:=0) hε x=0 := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [originalRow_ae 𝓕 μ H D (Function.uncurry S.value) S.predictable hε x,
      ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealL2) 2
        ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hp hz
    have hp0 : ¬ ((p.1:ℝ)<(0:ℝ)) := not_lt.mpr p.1.2
    simp only [hp,ite_eq_right hp0,hz,Pi.zero_apply]
  have he := S.equation 0 (show (0:ℝ≥0)≤H from bot_le) ε hε x
  simp only [NNReal.coe_zero,zero_add] at he
  rw [hr,map_zero] at he
  filter_upwards [he,Lp.coeFn_zero ℝ 2 μ] with ω hω hz
  rw [hω,hz]
  simp only [Pi.zero_apply,add_zero]
end SHE.OriginalNativePastIncrement
