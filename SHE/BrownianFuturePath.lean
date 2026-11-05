module
public import SHE.BrownianFutureCylinders
public import SHE.CanonicalContinuousStateDriver
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.BrownianFuturePath
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω P ι:Type*}[MeasurableSpace Ω][MeasurableSpace P][Countable ι][DecidableEq ι]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(X:ι→ℝ≥0→Ω→ℝ)(hc:∀i ω,Continuous (fun t=>X i t ω))
variable(hX:∀i t,Measurable[𝓕 t] (X i t))
variable(hBrown:∀n (a:Fin n→ι),FiniteBrownianLawOn 𝓕 μ H (fun i=>X (a i))
  (fun i j=>if a i=a j then 1 else 0))

/-- The actual shifted countable future-driver path, with the original
coordinate process retained and its value at the restart subtracted. -/
def value(v h:ℝ≥0)(ω:Ω)(i:ι):C(Icc (0:ℝ) (h:ℝ),ℝ):=
  ⟨fun t=>X i (v+t.val.toNNReal) ω-X i v ω,
    (((hc i ω).comp (continuous_const.add (continuous_real_toNNReal.comp continuous_subtype_val))).sub continuous_const)⟩

include hX in
theorem measurable(v h:ℝ≥0):Measurable (value X hc v h):=by
  apply measurable_pi_iff.mpr
  intro i
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((hX i _).mono (𝓕.le _) le_rfl).sub ((hX i v).mono (𝓕.le _) le_rfl)

include hX hBrown in
/-- Actual finite Brownian increment independence determines the whole
conditional future path law on one original-prefix AE event. -/
theorem independent(v h:ℝ≥0)(hvh:v+h≤H)(Z:Ω→P)(hZ:Measurable[𝓕 v] Z):
    IndepFun Z (value X hc v h) μ:=by
  let V:Ω→(ι×Icc (0:ℝ) (h:ℝ)→ℝ):=
    fun ω p=>X p.1 (v+p.2.val.toNNReal) ω-X p.1 v ω
  have hi:IndepFun Z V μ:=BrownianFutureCylinders.full 𝓕 μ H X hX hBrown v
    ((le_add_of_nonneg_right h.property).trans hvh) Prod.fst
    (fun p:ι×Icc (0:ℝ) (h:ℝ)=>v+p.2.val.toNNReal)
    (fun p=>⟨le_add_of_nonneg_right (by positivity),
      (add_le_add_right (show p.2.val.toNNReal≤h by simpa only[Real.toNNReal_coe] using (Real.toNNReal_le_toNNReal p.2.property.2)) v).trans hvh⟩) Z hZ
  have hco:MeasurableSpace.comap (value X hc v h)
      (inferInstance:MeasurableSpace (ι→C(Icc (0:ℝ) (h:ℝ),ℝ)))≤
      MeasurableSpace.comap V inferInstance:=by
    apply Measurable.comap_le
    letI:MeasurableSpace Ω:=MeasurableSpace.comap V inferInstance
    apply measurable_pi_iff.mpr
    intro i
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    have hv:Measurable V:=Measurable.of_comap_le le_rfl
    change Measurable (fun ω=>V ω (i,t))
    exact (measurable_pi_apply (i,t)).comp hv
  exact indep_of_indep_of_le_right hi hco

include hX hBrown in
theorem conditional(v h:ℝ≥0)(hvh:v+h≤H)(Z:Ω→P)(hZ:Measurable[𝓕 v] Z):
    condDistrib (value X hc v h) Z μ=ᵐ[μ.map Z]
      Kernel.const P (μ.map (value X hc v h)):=
  BrownianConditionalIncrement.kernel_of_independent μ Z _
    (hZ.mono (𝓕.le _) le_rfl).aemeasurable (measurable 𝓕 X hc hX v h).aemeasurable
    (independent 𝓕 μ H X hc hX hBrown v h hvh Z hZ)
end SHE.BrownianFuturePath
