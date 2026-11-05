module

public import SHE.HaarHeatIntegrand
public import SHE.RealHeat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RealHaarIntegrand
open MeasureTheory Set AddCircle CircleHeat FiniteHaar HaarHeatIntegrand DyadicApproximation
open scoped ENNReal NNReal Topology
local instance realHaarIntegrand_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance realHaarIntegrand_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance realHaarIntegrand_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance realHaarIntegrand_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance realHaarIntegrand_stateSigma : MeasurableSpace RealL2 := borel RealL2
local instance realHaarIntegrand_stateBorel : BorelSpace RealL2 := ⟨rfl⟩

abbrev Columns := HilbertColumns.Space HaarNode RealL2
local instance realHaarIntegrand_columnsSigma : MeasurableSpace Columns := borel Columns
local instance realHaarIntegrand_columnsBorel : BorelSpace Columns := ⟨rfl⟩
local instance realHaarIntegrand_complexColumnsSigma : MeasurableSpace HaarHeatIntegrand.Columns := borel HaarHeatIntegrand.Columns
local instance realHaarIntegrand_complexColumnsBorel : BorelSpace HaarHeatIntegrand.Columns := ⟨rfl⟩

theorem realPart_norm {v : CircleL2} (hv : ∀ᵐ x ∂haarAddCircle,(v x).im=0) : ‖realPart v‖=‖v‖ := by
  let w : realCircleSpace := ⟨v,(mem_realCircleSpace v).mpr hv⟩
  exact realCircleIdentification.symm.norm_map w

theorem kernel_column_real {ell M : ℝ} (hell : 0 < ell) (p : ℝ × EllipticField ell M) (q : HaarNode) :
    ∀ᵐ x ∂haarAddCircle,(HaarHeatIntegrand.kernel ell M hell p q x).im=0 := by
  rw [kernel_apply]
  split_ifs with ht
  · exact RealHeat.heat_real _ _ (globalHaarColumn_real_ae q p.2.1 p.2.2.1)
  · filter_upwards [Lp.coeFn_zero ℂ 2 haarAddCircle] with x hx
    rw [hx]
    rfl

theorem kernel_realPart_summable {ell M : ℝ} (hell : 0 < ell) (p : ℝ × EllipticField ell M) :
    Summable (fun q => ‖realPart (HaarHeatIntegrand.kernel ell M hell p q)‖^2) := by
  have hh := (lp.hasSum_norm (by norm_num : 0 < (2:ENNReal).toReal)
    (HaarHeatIntegrand.kernel ell M hell p)).summable
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,realPart_norm (kernel_column_real hell p _)] using hh

def kernel (ell M : ℝ) (hell : 0 < ell) (p : ℝ × EllipticField ell M) : Columns :=
  HilbertColumns.ofSummable (fun q => realPart (HaarHeatIntegrand.kernel ell M hell p q))
    (kernel_realPart_summable hell p)

theorem kernel_apply (ell M : ℝ) (hell : 0 < ell) (p : ℝ × EllipticField ell M) (q : HaarNode) :
    kernel ell M hell p q=realPart (HaarHeatIntegrand.kernel ell M hell p q) := rfl

theorem kernel_measurable (ell M : ℝ) (hell : 0 < ell) : Measurable (kernel ell M hell) := by
  apply HilbertColumns.measurable_of_columns
  intro q
  have hc : Measurable (fun p => HaarHeatIntegrand.kernel ell M hell p q) := by
    have hm := (HaarHeatIntegrand.kernel_measurable ell M hell)
    exact ((lp.evalCLM ℝ (fun _ : HaarNode => CircleL2) 2 q).continuous.measurable).comp hm
  exact (Complex.reCLM.compLpL 2 haarAddCircle).continuous.measurable.comp hc

theorem kernel_norm_sq (ell M : ℝ) (hell : 0 < ell) (p : ℝ × EllipticField ell M) :
    ‖kernel ell M hell p‖^2=‖HaarHeatIntegrand.kernel ell M hell p‖^2 := by
  rw [HilbertColumns.norm_sq,HilbertColumns.norm_sq]
  apply tsum_congr
  intro q
  rw [kernel_apply,realPart_norm (kernel_column_real hell p q)]

theorem kernel_difference_norm_sq (ell M : ℝ) (hell : 0 < ell) (p r : ℝ × EllipticField ell M) :
    ‖kernel ell M hell p-kernel ell M hell r‖^2=
      ‖HaarHeatIntegrand.kernel ell M hell p-HaarHeatIntegrand.kernel ell M hell r‖^2 := by
  rw [HilbertColumns.norm_sq,HilbertColumns.norm_sq]
  apply tsum_congr
  intro q
  change ‖kernel ell M hell p q-kernel ell M hell r q‖^2=
    ‖HaarHeatIntegrand.kernel ell M hell p q-HaarHeatIntegrand.kernel ell M hell r q‖^2
  rw [kernel_apply,kernel_apply]
  have hr : ∀ᵐ x ∂haarAddCircle,
      ((HaarHeatIntegrand.kernel ell M hell p q-HaarHeatIntegrand.kernel ell M hell r q) x).im=0 := by
    filter_upwards [kernel_column_real hell p q,kernel_column_real hell r q,
      Lp.coeFn_sub (HaarHeatIntegrand.kernel ell M hell p q) (HaarHeatIntegrand.kernel ell M hell r q)] with x hp hr hx
    rw [hx]
    change ((HaarHeatIntegrand.kernel ell M hell p q x)-(HaarHeatIntegrand.kernel ell M hell r q x)).im=0
    simp only [Complex.sub_im,hp,hr,sub_self]
  change ‖(Complex.reCLM.compLpL 2 haarAddCircle) (HaarHeatIntegrand.kernel ell M hell p q)-
    (Complex.reCLM.compLpL 2 haarAddCircle) (HaarHeatIntegrand.kernel ell M hell r q)‖^2=_
  rw [← map_sub]
  change ‖realPart (HaarHeatIntegrand.kernel ell M hell p q-HaarHeatIntegrand.kernel ell M hell r q)‖^2=_
  exact congrArg (fun z : ℝ => z^2) (realPart_norm hr)

end SHE.RealHaarIntegrand
