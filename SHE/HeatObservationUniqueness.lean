module

public import SHE.HeatPhysicalSubsequence
public import SHE.NativeRepresentativeEnergy
public import SHE.NativeHeatObservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.HeatObservationUniqueness
open MeasureTheory AddCircle StoppedFourier NativeHeatObservation DyadicApproximation Filter Topology
local instance observationUnique_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance observationUnique_realSigma : MeasurableSpace RealL2:=borel _
local instance observationUnique_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance observationUnique_circleSigma : MeasurableSpace CircleL2:=borel _
local instance observationUnique_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

/-- All positive heat observations of two measurable original Hilbert
states determine the SAME actual states almost everywhere. No state
moment, spatial version or stochastic integral is an extra premise. -/
theorem ae_eq_small (μ:Measure Ω) [IsFiniteMeasure μ] (U V:Ω→RealL2)
    (hU:Measurable U) (hV:Measurable V)
    (r : ℝ) (hr : 0 < r)
    (hobs:∀ε:ℝ,0<ε→ε<r→∀x:HeatCircle,
      (fun ω=>functional ε x (U ω))=ᵐ[μ] fun ω=>functional ε x (V ω)):
    U=ᵐ[μ] V:=by
  obtain ⟨ε₀,hε₀,hlim₀,hphysical₀⟩:=HeatPhysicalSubsequence.exists_common_subsequence U V hU hV μ
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp (hlim₀.eventually (gt_mem_nhds hr))
  let ε : ℕ → ℝ := fun n => ε₀ (n+K)
  have hε (n : ℕ) : 0 < ε n := hε₀ _
  have hsmall (n : ℕ) : ε n < r := hK _ (by omega)
  have hphysical : ∀ᵐ p ∂μ.prod (haarAddCircle (T := 2*Real.pi)),
      Tendsto (fun n => PhysicalProfile.physicalHeatMean (embed (U p.1)) (ε n,p.2))
        atTop (𝓝 (PredictableScalarField.nativeField U p)) ∧
      Tendsto (fun n => PhysicalProfile.physicalHeatMean (embed (V p.1)) (ε n,p.2))
        atTop (𝓝 (PredictableScalarField.nativeField V p)) := by
    filter_upwards [hphysical₀] with p hp
    exact ⟨hp.1.comp (tendsto_add_atTop_nat K),hp.2.comp (tendsto_add_atTop_nat K)⟩
  have hm (Y:Ω→RealL2) (hY:Measurable Y) (t:ℝ):
      Measurable (fun p:HeatCircle×Ω=>PhysicalProfile.physicalHeatMean (embed (Y p.2)) (t,p.1)):=
    PhysicalProfile.physicalHeatMean_joint_measurable.comp
      (((embed.continuous.measurable.comp hY).comp measurable_snd).prodMk
        ((measurable_const (a:=t)).prodMk measurable_fst))
  have hj(n:ℕ):∀ᵐp:Ω×HeatCircle ∂μ.prod haarAddCircle,
      PhysicalProfile.physicalHeatMean (embed (U p.1)) (ε n,p.2)=
        PhysicalProfile.physicalHeatMean (embed (V p.1)) (ε n,p.2):=by
    have hs:∀ᵐp:HeatCircle×Ω ∂haarAddCircle.prod μ,
        PhysicalProfile.physicalHeatMean (embed (U p.2)) (ε n,p.1)=
          PhysicalProfile.physicalHeatMean (embed (V p.2)) (ε n,p.1):=by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (hm U hU _) (hm V hV _))).mpr
      filter_upwards with x
      filter_upwards [hobs (ε n) (hε n) (hsmall n) x] with ω hω
      simpa only [functional_physical (hε n)] using hω
    exact (Measure.measurePreserving_swap (μ:=μ) (ν:=haarAddCircle)).quasiMeasurePreserving.ae hs
  have hnative:∀ᵐp:Ω×HeatCircle ∂μ.prod haarAddCircle,
      PredictableScalarField.nativeField U p=PredictableScalarField.nativeField V p:=by
    filter_upwards [hphysical,ae_all_iff.mpr hj] with p hp ho
    have he:(fun n=>PhysicalProfile.physicalHeatMean (embed (U p.1)) (ε n,p.2))=
        (fun n=>PhysicalProfile.physicalHeatMean (embed (V p.1)) (ε n,p.2)):=funext ho
    rw [he] at hp
    exact tendsto_nhds_unique hp.1 hp.2
  filter_upwards [Measure.ae_ae_of_ae_prod hnative] with ω hω
  have he:=NativeRepresentativeEnergy.section_energy U V ω
  have hz:(∫x:HeatCircle,(PredictableScalarField.nativeField V (ω,x)-
      PredictableScalarField.nativeField U (ω,x))^2 ∂haarAddCircle)=0:=by
    calc
      _=∫x:HeatCircle,(0:ℝ) ∂haarAddCircle:=by
        apply integral_congr_ae
        filter_upwards [hω] with x hx
        rw [hx,sub_self,zero_pow (by norm_num : (2:ℕ)≠0)]
      _=0:=integral_zero _ _
  have hn:‖V ω-U ω‖^2=0:=he.symm.trans hz
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))).symm

/-- All positive heat observations determine the actual state; this
interface is retained as a specialization of the small-age theorem. -/
theorem ae_eq (μ:Measure Ω) [IsFiniteMeasure μ] (U V:Ω→RealL2)
    (hU:Measurable U) (hV:Measurable V)
    (hobs:∀ε:ℝ,0<ε→∀x:HeatCircle,
      (fun ω=>functional ε x (U ω))=ᵐ[μ] fun ω=>functional ε x (V ω)):
    U=ᵐ[μ] V :=
  ae_eq_small μ U V hU hV 1 (by norm_num) (fun ε hε _ x => hobs ε hε x)

end SHE.HeatObservationUniqueness
