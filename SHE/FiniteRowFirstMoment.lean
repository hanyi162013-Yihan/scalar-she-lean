module

public import SHE.StopWeightedInput
public import SHE.SectionEnergy
public import SHE.ParentDensityMass
public import SHE.CouplingLaws

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.StopWeightedRows
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion FiniteHeatRows
open scoped ENNReal BigOperators
local instance finiteRowFirstMoment_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance finiteRowFirstMoment_circleSigma : MeasurableSpace CircleL2 := borel _
local instance finiteRowFirstMoment_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance finiteRowFirstMoment_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
variable {n : ℕ}

theorem kernel_continuous (Λ : ℝ) (Z : Fin n→Observation) (q r : ℝ) :
    Continuous (fun D : WordRecursion.State n→L[ℝ]ℝ=>kernel D Λ Z q r) := by
  have he : (fun D : WordRecursion.State n→L[ℝ]ℝ=>kernel D Λ Z q r)=
      fun D=>∑ i : Fin n,((FiniteHeatRows.coefficient D i*weights Λ Z q i:ℝ):ℂ) •
        circleHeat ((Z i).target-r) (Z i).center := funext (fun D=>kernel_eq_sum D Λ Z q r)
  rw [he]
  apply continuous_finsetSum
  intro i _
  have hd : Continuous (fun D : WordRecursion.State n→L[ℝ]ℝ=>FiniteHeatRows.coefficient D i):=
    continuous_id.clm_apply continuous_const
  have hc : Continuous (fun D : WordRecursion.State n→L[ℝ]ℝ=>
      ((FiniteHeatRows.coefficient D i*weights Λ Z q i:ℝ):ℂ)):=
    Complex.continuous_ofReal.comp (hd.mul_const _)
  exact hc.smul (continuous_const (y:=circleHeat ((Z i).target-r) (Z i).center))

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Pointwise native physical row moments give the actual Hilbert-row
energy by ordinary product Fubini, retaining the input variable until
after its true heat mass has been integrated. -/
theorem kernel_second_moment (D : Ω→WordRecursion.State n→L[ℝ]ℝ) (hD : Measurable D)
    (Λ : ℝ) (Z : Fin n→Observation) (q r : ℝ) (hr : ∀ i,r<(Z i).target)
    (hP : Measurable (fun z : HeatCircle×Ω=>D z.2 (weightedHeatRow Λ Z q r z.1)))
    (B : HeatCircle→ℝ) (hB : Integrable B haarAddCircle)
    (hs : ∀ᵐ y ∂haarAddCircle,
      Integrable (fun ω=>|D ω (weightedHeatRow Λ Z q r y)|^2) μ ∧
      (∫ ω,|D ω (weightedHeatRow Λ Z q r y)|^2 ∂μ)≤B y) :
    Integrable (fun ω=>‖kernel (D ω) Λ Z q r‖^2) μ ∧
      (∫ ω,‖kernel (D ω) Λ Z q r‖^2 ∂μ)≤∫ y,B y ∂haarAddCircle := by
  let P : HeatCircle×Ω→ℝ:=fun z=>D z.2 (weightedHeatRow Λ Z q r z.1)
  have hj:=SectionEnergy.product_energy μ haarAddCircle P hP B hB
    (by simpa only [Real.norm_eq_abs] using hs.mono (fun _ h=>h.1))
    (by simpa only [Real.norm_eq_abs] using hs.mono (fun _ h=>h.2))
  have he (ω : Ω) : ‖kernel (D ω) Λ Z q r‖^2=∫ y,‖P (y,ω)‖^2 ∂haarAddCircle := by
    rw [L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [kernel_ae (D ω) Λ Z q r hr] with y hy
    rw [hy]
    simp only [Complex.norm_real,Real.norm_eq_abs,P]
  have hi:=hj.1.integral_prod_right.congr (ae_of_all _ (fun ω=>(he ω).symm))
  refine ⟨hi,?_⟩
  rw [integral_congr_ae (ae_of_all _ he),←integral_prod_symm _ hj.1]
  exact hj.2

/-- A correlated current input is paired with the ACTUAL finite
physical row, with no independence premise. This is an absolute L1
bound before old-space averaging or cancellation. -/
theorem input_first_moment (D : Ω→WordRecursion.State n→L[ℝ]ℝ) (hD : Measurable D)
    (Λ : ℝ) (Z : Fin n→Observation) (q : ℝ) (hq : ∀ i,q<(Z i).target)
    (V : Ω→CircleL2) (hV : Measurable V) (hVi : Integrable (fun ω=>‖V ω‖^2) μ)
    (hKi : Integrable (fun ω=>‖kernel (D ω) Λ Z q q‖^2) μ)
    (A : ℝ) (hA : 0≤A) (hK : (∫ ω,‖kernel (D ω) Λ Z q q‖^2 ∂μ)≤A^2) :
    Integrable (fun ω=>D ω (PhysicalMeanRange.dampedDirection
      (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>NativeHeatSpan.unitCenter (Z i).center) q Λ (V ω))) μ ∧
      (∫ ω,|D ω (PhysicalMeanRange.dampedDirection
        (fun i=>(Z i).stop) (fun i=>(Z i).target)
        (fun i=>NativeHeatSpan.unitCenter (Z i).center) q Λ (V ω))| ∂μ)≤
          sqrt (∫ ω,‖V ω‖^2 ∂μ)*A := by
  let K : Ω→CircleL2:=fun ω=>kernel (D ω) Λ Z q q
  have hKm : Measurable K:=(kernel_continuous Λ Z q q).measurable.comp hD
  have hKp : MemLp K 2 μ:=(memLp_two_iff_integrable_sq_norm hKm.aestronglyMeasurable).mpr hKi
  have hVp : MemLp V 2 μ:=(memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr hVi
  have hprod : Integrable (fun ω=>‖K ω‖*‖V ω‖) μ:=hKp.norm.integrable_mul hVp.norm
  have hbound (ω : Ω) : |(inner ℂ (K ω) (V ω)).re|≤‖K ω‖*‖V ω‖:=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hM : Measurable (fun ω=>(inner ℂ (K ω) (V ω)).re):=
    Complex.continuous_re.measurable.comp (continuous_inner.measurable.comp (hKm.prodMk hV))
  have hi : Integrable (fun ω=>(inner ℂ (K ω) (V ω)).re) μ:=
    hprod.mono' hM.aestronglyMeasurable (ae_of_all _ hbound)
  have hh:=integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp K (ENNReal.ofReal (2:ℝ)) μ by simpa using hKp)
    (show MemLp V (ENNReal.ofReal (2:ℝ)) μ by simpa using hVp)
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow] at hh
  have hroot : sqrt (∫ ω,‖K ω‖^2 ∂μ)≤A:=
    (Real.sqrt_le_iff).mpr ⟨hA,hK⟩
  have hinput : ∀ ω,D ω (PhysicalMeanRange.dampedDirection
      (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>NativeHeatSpan.unitCenter (Z i).center) q Λ (V ω))=(inner ℂ (K ω) (V ω)).re:=
    fun ω=>StopWeightedInput.functional_dampedDirection (D ω) Λ q Z hq (V ω)
  simp_rw [hinput]
  refine ⟨hi,?_⟩
  exact (integral_mono hi.norm hprod hbound).trans
    (hh.trans ((mul_le_mul_of_nonneg_right hroot (sqrt_nonneg _)).trans_eq (mul_comm _ _)))

end SHE.StopWeightedRows
