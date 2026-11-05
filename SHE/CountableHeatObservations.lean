module
public import SHE.HeatObservationUniqueness
public import SHE.NativeHeatFunctionalEnergy
public import Mathlib.Topology.DenseEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.CountableHeatObservations
open MeasureTheory AddCircle StoppedFourier NativeHeatObservation DyadicApproximation Filter Topology
open scoped ENNReal
local instance countableHeatObservations_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance countableHeatObservations_realSigma : MeasurableSpace RealL2:=borel _
local instance countableHeatObservations_realBorel : BorelSpace RealL2:=⟨rfl⟩

/-- Literal native-circle heat observations are continuous in their center. -/
theorem continuous_center {ε:ℝ}(hε:0<ε)(u:RealL2):
    Continuous (fun x:HeatCircle=>functional ε x u):=by
  have hc:Continuous (fun x:HeatCircle=>PhysicalProfile.heatMeanSeries (embed u) (ε,x)):=by
    unfold PhysicalProfile.heatMeanSeries
    apply continuous_tsum (fun n=>by fun_prop) (heat_fourier_series_norm_summable hε (embed u))
    intro n x
    simp only[norm_mul,show ‖fourier n x‖=1 from Circle.norm_coe _,mul_one]
    exact le_rfl
  have he:(fun x:HeatCircle=>functional ε x u)=
      fun x=>(PhysicalProfile.heatMeanSeries (embed u) (ε,x)).re:=by
    funext x
    exact functional_physical hε x u
  rw[he]
  exact Complex.continuous_re.comp hc

/-- Dense countable centers determine each genuine heat-smoothed state. -/
theorem heat_eq {ε:ℝ}(hε:0<ε)(c:ℕ→HeatCircle)(hc:DenseRange c)(u v:RealL2)
    (ho:∀j,functional ε (c j) u=functional ε (c j) v):
    heat ε u=heat ε v:=by
  have hall:(fun x:HeatCircle=>functional ε x u)=(fun x=>functional ε x v):=
    hc.equalizer (continuous_center hε u) (continuous_center hε v) (funext ho)
  have hn:=NativeRepresentativeEnergy.section_energy
    (fun _:Unit=>heat ε u) (fun _:Unit=>heat ε v) ()
  have hz:(∫x:HeatCircle,
      (PredictableScalarField.nativeField (fun _:Unit=>heat ε v) ((),x)-
       PredictableScalarField.nativeField (fun _:Unit=>heat ε u) ((),x))^2 ∂haarAddCircle)=0:=by
    calc
      _=∫_x:HeatCircle,(0:ℝ) ∂haarAddCircle:=by
        apply integral_congr_ae
        filter_upwards[NativeHeatFunctionalEnergy.functional_ae hε u,
          NativeHeatFunctionalEnergy.functional_ae hε v] with x hu hv
        rw[←hu,←hv,congrFun hall x,sub_self,zero_pow (by norm_num:(2:ℕ)≠0)]
      _=0:=integral_zero _ _
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (hn.symm.trans hz)))).symm

/-- Any fixed positive heat-age sequence tending to zero, together with
countably many dense centers, separates the original real Hilbert states. -/
theorem eq_of_observations (ε:ℕ→ℝ)(hε:∀n,0<ε n)(hε0:Tendsto ε atTop (𝓝 0))
    (c:ℕ→HeatCircle)(hc:DenseRange c)(u v:RealL2)
    (ho:∀n j,functional (ε n) (c j) u=functional (ε n) (c j) v):u=v:=by
  have hu:=PositiveGapObservations.continuous_heat_action.tendsto (0,u) |>.comp
    (hε0.prodMk_nhds (tendsto_const_nhds (x:=u)))
  have hv:=PositiveGapObservations.continuous_heat_action.tendsto (0,v) |>.comp
    (hε0.prodMk_nhds (tendsto_const_nhds (x:=v)))
  have he:(fun n=>heat (ε n) u)=(fun n=>heat (ε n) v):=
    funext (fun n=>heat_eq (hε n) c hc u v (ho n))
  change Tendsto (fun n=>heat (ε n) u) atTop (𝓝 (heat 0 u)) at hu
  change Tendsto (fun n=>heat (ε n) v) atTop (𝓝 (heat 0 v)) at hv
  rw[he] at hu
  have hh:=tendsto_nhds_unique hu hv
  simpa only[heat,zero_div,RealHeat.realHeat_zero,ContinuousLinearMap.id_apply] using hh

/-- A concrete countable family, fixed independently of states and measures. -/
def age(n:ℕ):ℝ:=1/((n:ℝ)+1)
def center:ℕ→HeatCircle:=TopologicalSpace.denseSeq HeatCircle

theorem age_pos(n:ℕ):0<age n:=by unfold age;positivity
theorem age_tendsto:Tendsto age atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
theorem center_dense:DenseRange center:=TopologicalSpace.denseRange_denseSeq _

theorem eq (u v:RealL2)
    (ho:∀n j,functional (age n) (center j) u=functional (age n) (center j) v):u=v:=
  eq_of_observations age age_pos age_tendsto center center_dense u v ho

variable{Ω:Type*}[MeasurableSpace Ω]
/-- One event for all countably many scalar observations gives one event
of original state equality. No state integrability is needed. -/
theorem ae_eq (μ:Measure Ω)(U V:Ω→RealL2)
    (ho:∀n j,(fun ω=>functional (age n) (center j) (U ω))=ᵐ[μ]
      fun ω=>functional (age n) (center j) (V ω)):U=ᵐ[μ] V:=by
  have hall:∀ᵐω∂μ,∀n j,functional (age n) (center j) (U ω)=
      functional (age n) (center j) (V ω):=
    ae_all_iff.mpr (fun n=>ae_all_iff.mpr (ho n))
  exact hall.mono (fun ω hω=>eq (U ω) (V ω) hω)
end SHE.CountableHeatObservations
