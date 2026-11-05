module
public import SHE.DeterministicItoShiftPull
public import SHE.OriginalNativePastIncrement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
set_option linter.unusedSectionVars false
namespace SHE.ShiftedOriginalNativeEquation
open MeasureTheory Set PredictableL2 NativeHeatObservation FiniteHaar DyadicApproximation
open OrthogonalItoChannels StoppedFourier PredictableScalarHaarRotation
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace (Both RealL2):=borel _
local instance : BorelSpace (Both RealL2):=⟨rfl⟩
variable{Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(D:SmoothApproximation.ScalarData)
variable(B:StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)(u₀:RealL2)
variable(S:OriginalNativeHeatEquation.Data 𝓕 μ H D B u₀)

/-- A random-initial observable model is kept separate from the
fixed deterministic-initial model used by local law uniqueness. -/
structure RandomInitialData(ξ:Ω→RealL2) where
  initial_measurable:StronglyMeasurable[𝓕 0] ξ
  value:ℝ≥0→Ω→RealL2
  initial:value 0=ξ
  continuous:∀ω,Continuous (fun t=>value t ω)
  predictable:StronglyMeasurable[𝓕.predictable] (Function.uncurry value)
  equation:∀q:ℝ≥0,q≤H→∀(ε:ℝ)(hε:0<ε)(x:HeatCircle),
    (fun ω=>functional ε x (value q ω))=ᵐ[μ]
      (fun ω=>functional ε x (heat (q:ℝ) (ξ ω))+B.integral
        (originalRow 𝓕 μ H D (Function.uncurry value) predictable
          (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x) ω)

variable(v h:ℝ≥0)(hvh:v+h≤H)
local notation "FS"=>DeterministicItoShift.filtration 𝓕 v
local notation "BS"=>DeterministicItoShift.integral 𝓕 μ H v h hvh B

def state(t:ℝ≥0)(ω:Ω):RealL2:=S.value (v+t) ω

theorem state_predictable:StronglyMeasurable[(FS).predictable]
    (Function.uncurry (state 𝓕 μ H D B u₀ S v)):=
  DeterministicItoShift.pull_predictable 𝓕 v (Function.uncurry S.value) S.predictable

def row(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    Process (E:=Both RealL2) FS μ h:=
  originalRow FS μ h D (Function.uncurry (state 𝓕 μ H D B u₀ S v))
    (state_predictable 𝓕 μ H D B u₀ S v) (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x

def original_row(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    Process (E:=Both RealL2) 𝓕 μ H:=
  originalRow 𝓕 μ H D (Function.uncurry S.value) S.predictable
    (T:=((v+q:ℝ≥0):ℝ)+ε) (t:=((v+q:ℝ≥0):ℝ)) (by linarith) x


include hvh in
/-- The shifted original observation input is precisely the pull of
its actual absolute-target original input. -/
theorem row_eq_pull(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    row 𝓕 μ H D B u₀ S v h q ε hε x=
      DeterministicItoShift.pull 𝓕 v μ H h hvh
        (original_row 𝓕 μ H D B u₀ S v q ε hε x):=by
  apply PastItoAlgebra.eq_of_ambient_ae
  have habs:=originalRow_ae 𝓕 μ H D (Function.uncurry S.value) S.predictable
    (T:=((v+q:ℝ≥0):ℝ)+ε) (t:=((v+q:ℝ≥0):ℝ)) (by linarith) x
  have habs':=(DeterministicItoShift.product_translation μ H v h hvh).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (s:=Ioc v (v+h)×ˢuniv) habs)
  have hloc:=originalRow_ae FS μ h D (Function.uncurry (state 𝓕 μ H D B u₀ S v))
    (state_predictable 𝓕 μ H D B u₀ S v) (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x
  filter_upwards [hloc,habs',DeterministicItoShift.pull_ae 𝓕 v μ H h hvh
    (original_row 𝓕 μ H D B u₀ S v q ε hε x)] with p hl ha hp
  change row 𝓕 μ H D B u₀ S v h q ε hε x p=_ at hl ⊢
  rw [hl,hp]
  change original_row 𝓕 μ H D B u₀ S v q ε hε x (v+p.1,p.2)=_ at ha
  rw [ha]
  have hgap:(((v+q:ℝ≥0):ℝ)+ε)-((v+p.1:ℝ≥0):ℝ)=(q:ℝ)+ε-(p.1:ℝ):=by
    push_cast
    ring
  have hcut:((v+p.1:ℝ≥0):ℝ)<((v+q:ℝ≥0):ℝ)↔(p.1:ℝ)<(q:ℝ):=by
    simp only [NNReal.coe_add,add_lt_add_iff_left]
  simp only [hgap,hcut,Function.uncurry,state]

include hvh in
/-- The exact shifted input realizes the original post-v stochastic
increment, with no auxiliary integral or version premise. -/
theorem integral_row(q:ℝ≥0)(hq:q≤h)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    (BS).integral (row 𝓕 μ H D B u₀ S v h q ε hε x)=
      B.integral (PastItoInputs.post 𝓕 μ H v (original_row 𝓕 μ H D B u₀ S v q ε hε x)):=by
  rw [row_eq_pull 𝓕 μ H D B u₀ S v h hvh q ε hε x,
    DeterministicItoShift.integral_pull]
  congr 1
  apply DeterministicItoShift.window_eq_post 𝓕 v μ H h hvh
  have ha:=originalRow_ae 𝓕 μ H D (Function.uncurry S.value) S.predictable
    (T:=((v+q:ℝ≥0):ℝ)+ε) (t:=((v+q:ℝ≥0):ℝ)) (by linarith) x
  filter_upwards [ha] with p hp hph
  change original_row 𝓕 μ H D B u₀ S v q ε hε x p=_ at hp ⊢
  rw [hp]
  have hqv:v+q≤v+h:=by gcongr
  have hn:¬(p.1:ℝ)<((v+q:ℝ≥0):ℝ):=by
    apply not_lt.mpr
    exact_mod_cast hqv.trans hph.le
  exact ite_eq_right hn

include hvh in
/-- A genuine random-initial original observable model at deterministic
past v, on the ORIGINAL probability space and original shifted integral.
No conditional kernel or deterministic-initial uniqueness is assumed. -/
def of_original:RandomInitialData FS μ h D BS (S.value v) where
  initial_measurable:=by
    have hi:StronglyMeasurable[𝓕 v] (S.value v):=
      (show IsStronglyPredictable 𝓕 S.value from S.predictable).stronglyAdapted v
    change StronglyMeasurable[𝓕 (v+0)] (S.value v)
    rw [_root_.add_zero]
    exact hi
  value:=state 𝓕 μ H D B u₀ S v
  initial:=by funext ω;simp only [state,_root_.add_zero]
  continuous:=fun ω=>(S.continuous ω).comp (continuous_const.add continuous_id)
  predictable:=state_predictable 𝓕 μ H D B u₀ S v
  equation:=by
    intro q hq ε hε x
    have hvqH:v+q≤H:=(by gcongr : v+q≤v+h).trans hvh
    have he:=OriginalNativePastIncrement.restart_observation 𝓕 μ H D B u₀ S v q hvqH ε hε x
    change (fun ω=>functional ε x (S.value (v+q) ω))=ᵐ[μ]
      (fun ω=>functional ε x (heat (q:ℝ) (S.value v ω))+
        B.integral (PastItoInputs.post 𝓕 μ H v
          (original_row 𝓕 μ H D B u₀ S v q ε hε x)) ω) at he
    rw [←integral_row 𝓕 μ H D B u₀ S v h hvh q hq ε hε x] at he
    exact he

end SHE.ShiftedOriginalNativeEquation
