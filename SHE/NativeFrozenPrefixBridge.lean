module

public import SHE.NativeCanonicalReferenceObservation
public import SHE.PastTwoChannelAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeFrozenPrefixBridge
open Set MeasureTheory PredictableL2 StoppedFourier FiniteHaar NativeHeatObservation
open scoped NNReal ENNReal
local instance nativeFrozenPrefixBridge_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeFrozenPrefixBridge_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance nativeFrozenPrefixBridge_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b q v : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (hbH : b≤H) (hqb : q<b)

theorem row_eq (x : HeatCircle) :
    NativeFrozenSpatialObservation.row 𝓕 μ H b q v hell hM f hf hbH hqb.le x 0=
      StoppedItoInputs.stop 𝓕 μ H q (PastItoInputs.post 𝓕 μ H v
        (NativeObservationProcess.process 𝓕 μ H hell hM f hf
          (show (q:ℝ)<(b:ℝ) by exact_mod_cast hqb) x)) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  let R:=NativeObservationProcess.process 𝓕 μ H hell hM f hf
    (show (q:ℝ)<(b:ℝ) by exact_mod_cast hqb) x
  have hr:=NativeObservationProcess.process_ae 𝓕 μ H hell hM f hf
    (show (q:ℝ)<(b:ℝ) by exact_mod_cast hqb) x
  filter_upwards [PastItoInputs.post_ae 𝓕 μ H v
      (FullHorizonEndpoint.process 𝓕 μ H q hell hM f hf
        (show (q:ℝ)≤(b:ℝ)+max (0:ℝ) 0 by simpa using (show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb.le)) x (hqb.le.trans hbH)),
    FullHorizonEndpoint.process_ae 𝓕 μ H q hell hM f hf
      (show (q:ℝ)≤(b:ℝ)+max (0:ℝ) 0 by simpa using (show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb.le)) x (hqb.le.trans hbH),
    StoppedItoInputs.stop_ae 𝓕 μ H q (PastItoInputs.post 𝓕 μ H v R),
    PastItoInputs.post_ae 𝓕 μ H v R,hr] with p hp hf hs hpost hr
  change NativeFrozenSpatialObservation.row 𝓕 μ H b q v hell hM f _ hbH hqb.le x 0 p=_ at hp
  rw [hp,hs]
  by_cases hq : (p.1:ℝ)<(q:ℝ)
  · rw [indicator_of_mem (show p∈StoppedItoInputs.before (Ω:=Ω) (q:ℝ) from hq),hpost]
    by_cases hv : v<p.1
    · rw [ite_eq_left hv,ite_eq_left hv,hf,hr,FullHorizonEndpoint.raw,
        indicator_of_mem (show p∈StoppedItoInputs.before (Ω:=Ω) (q:ℝ) from hq),
        NativeObservationProcess.integrand_eq hell f (show (q:ℝ)<(b:ℝ) by exact_mod_cast hqb),ite_eq_left hq]
      simp only [NativeObservationEndpoint.fullIntegrand,max_self,add_zero,
        ite_eq_left (hq.trans (show (q:ℝ)<(b:ℝ) by exact_mod_cast hqb))]
    · rw [ite_eq_right hv,ite_eq_right hv]
  · rw [indicator_of_notMem (show p∉StoppedItoInputs.before (Ω:=Ω) (q:ℝ) from hq)]
    rw [hf,FullHorizonEndpoint.raw,indicator_of_notMem (show p∉StoppedItoInputs.before (Ω:=Ω) (q:ℝ) from hq)]
    split_ifs <;> rfl

end SHE.NativeFrozenPrefixBridge
