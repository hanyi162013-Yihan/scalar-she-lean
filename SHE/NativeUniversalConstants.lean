module

public import SHE.NativeReserveTranslatedEnvelope
public import SHE.NativeMeanAveraging

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u
namespace SHE.NativeUniversalConstants
local instance nativeUniversalConstants_circleSigma : MeasurableSpace HeatTorus.CircleL2:=borel _
local instance nativeUniversalConstants_circleBorel : BorelSpace HeatTorus.CircleL2:=⟨rfl⟩

def rowHorizon (n:ℕ):ℝ:=Classical.choose (NativeReserveTranslatedEnvelope.joint_parent_envelope n)
def rowConstant (n:ℕ):ℝ:=Classical.choose
  (Classical.choose_spec (NativeReserveTranslatedEnvelope.joint_parent_envelope n))

def row_spec (n:ℕ):=
  Classical.choose_spec (Classical.choose_spec (NativeReserveTranslatedEnvelope.joint_parent_envelope n))

theorem rowHorizon_pos (n:ℕ):0<rowHorizon n:=(row_spec n).1
theorem rowConstant_pos (n:ℕ):0<rowConstant n:=(row_spec n).2.1

def currentHorizon (n:ℕ)(hn:0<n):ℝ:=Classical.choose (NativeMeanAveraging.native_mean_score_one_input.{u} n hn)
def currentConstant (n:ℕ)(hn:0<n):ℝ:=Classical.choose
  (Classical.choose_spec (NativeMeanAveraging.native_mean_score_one_input.{u} n hn))

def current_spec (n:ℕ)(hn:0<n):=
  Classical.choose_spec (Classical.choose_spec (NativeMeanAveraging.native_mean_score_one_input.{u} n hn))

theorem currentHorizon_pos (n:ℕ)(hn:0<n):0<currentHorizon.{u} n hn:=(current_spec.{u} n hn).1
theorem currentHorizon_le_one (n:ℕ)(hn:0<n):currentHorizon.{u} n hn≤1:=(current_spec.{u} n hn).2.1
theorem currentConstant_pos (n:ℕ)(hn:0<n):0<currentConstant.{u} n hn:=(current_spec.{u} n hn).2.2.1

end SHE.NativeUniversalConstants
