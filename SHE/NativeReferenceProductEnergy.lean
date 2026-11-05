module

public import SHE.NativeReferenceFunctionalEnergy
public import SHE.SectionFirstMoment

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.NativeReferenceProductEnergy
open Set MeasureTheory AddCircle Real StoppedFourier NativeHeatObservation DyadicApproximation
open scoped ENNReal
local instance referenceProduct_period : Fact (0<2*π):=⟨by positivity⟩
local instance referenceProduct_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance referenceProduct_realSigma : MeasurableSpace RealL2:=borel _
local instance referenceProduct_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance referenceProduct_nativeSigma : MeasurableSpace CircleL2:=borel _
local instance referenceProduct_nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [SFinite μ]

/-- Original sample/spatial energy for a compatible reference root.
The original Hilbert noise may be arbitrarily dependent on past data. -/
theorem energy {s τ:ℝ} (hs:0≤s) (hτ:0<τ) (a:ℝ)
    (d N:Ω→RealL2) (hd:Measurable d) (hN:Measurable N)
    (hdi:Integrable (fun ω=>‖d ω‖^2) μ) (hNi:Integrable (fun ω=>‖N ω‖^2) μ):
    let f:=fun z:Ω×HeatCircle=>a*functional (s+τ) z.2 (d z.1)+functional τ z.2 (N z.1)
    Integrable (fun z=>f z^2) (μ.prod haarAddCircle) ∧
      (∫z,f z^2 ∂μ.prod haarAddCircle)≤
        2*a^2*(∫ω,‖d ω‖^2 ∂μ)+2*(∫ω,‖N ω‖^2 ∂μ):=by
  intro f
  have hmF(t:ℝ)(ht:0<t)(U:Ω→RealL2)(hU:Measurable U):
      Measurable (fun z:Ω×HeatCircle=>functional t z.2 (U z.1)):=by
    have hm:=PhysicalProfile.physicalHeatMean_joint_measurable.comp
      (((embed.continuous.measurable.comp hU).comp measurable_fst).prodMk
        ((measurable_const (a:=t)).prodMk measurable_snd))
    convert! hm using 1
    funext z
    exact functional_physical ht z.2 (U z.1)
  have hm:Measurable f:=(hmF (s+τ) (by linarith) d hd).const_mul a |>.add (hmF τ hτ N hN)
  have hsec(ω):Integrable (fun x:HeatCircle=>f (ω,x)^2) haarAddCircle ∧
      (∫x:HeatCircle,f (ω,x)^2 ∂haarAddCircle)≤2*a^2*‖d ω‖^2+2*‖N ω‖^2:=by
    have he:=NativeReferenceFunctionalEnergy.reference_energy hs hτ a (d ω) (N ω)
    refine ⟨he.1,he.2.trans_le ?_⟩
    have hn:‖heat τ (a•heat s (d ω)+N ω)‖≤|a| * ‖d ω‖+‖N ω‖:=by
      apply (RealHeat.realHeat_contraction _ _).trans
      apply (norm_add_le _ _).trans
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (RealHeat.realHeat_contraction _ _) (abs_nonneg a)) le_rfl
    have hh:=pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (|a| * ‖d ω‖-‖N ω‖),sq_abs a]
  have hmajor:Integrable (fun ω=>2*a^2*‖d ω‖^2+2*‖N ω‖^2) μ:=
    (hdi.const_mul (2*a^2)).add (hNi.const_mul 2)
  have hiMean:Integrable (fun ω=>∫x:HeatCircle,f (ω,x)^2 ∂haarAddCircle) μ:=by
    apply hmajor.mono' ((hm.pow_const 2).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_of_nonneg (integral_nonneg (fun x=>sq_nonneg _))]
    exact (hsec ω).2
  have hi:Integrable (fun z=>f z^2) (μ.prod haarAddCircle):=by
    apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun ω=>(hsec ω).1),?_⟩
    simpa only [Real.norm_eq_abs,abs_sq] using hiMean
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  have he:=integral_mono hiMean hmajor (fun ω=>(hsec ω).2)
  simpa only [integral_add (hdi.const_mul (2*a^2)) (hNi.const_mul 2),integral_const_mul] using he

end SHE.NativeReferenceProductEnergy
