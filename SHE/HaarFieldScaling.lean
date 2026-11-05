module

public import SHE.HaarScalarScaling
public import SHE.NonlinearHaarIntegrand
public import SHE.DampedHeatKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.HaarFieldScaling
open MeasureTheory Set AddCircle CircleHeat FiniteHaar NonlinearHaarIntegrand
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace LowBands.StateL2 := borel _
local instance : BorelSpace LowBands.StateL2 := ⟨rfl⟩

def scale {ell M : ℝ} (c : ℝ) (hc : 0<c) (f : EllipticField ell M) : EllipticField (c*ell) (c*M) := by
  refine ⟨c•f.1,?_,?_⟩
  · filter_upwards [Lp.coeFn_smul c f.1,f.2.1] with x hx hr
    rw [hx]
    simp only [Pi.smul_apply,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,hr,mul_zero,zero_mul,add_zero]
  · filter_upwards [Lp.coeFn_smul c f.1,f.2.2] with x hx hb
    rw [hx]
    simp only [Pi.smul_apply,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    exact ⟨mul_le_mul_of_nonneg_left hb.1 hc.le,mul_le_mul_of_nonneg_left hb.2 hc.le⟩

theorem continuous_scale {ell M : ℝ} (c : ℝ) (hc : 0<c) :
    Continuous (scale (ell := ell) (M := M) c hc) := by
  have hh : Continuous (fun f : EllipticField ell M => c•f.1) :=
    (continuous_const (y := c)).smul continuous_subtype_val
  convert hh.subtype_mk (p := fun g : CircleL2 =>
    (∀ᵐ y ∂haarAddCircle,(g y).im=0) ∧
      (∀ᵐ y ∂haarAddCircle,c*ell≤(g y).re ∧ (g y).re≤c*M))
    (fun f => (scale c hc f).2) using 1
  funext f
  apply Subtype.ext
  rfl

theorem complex_kernel_scale {ell M : ℝ} (hell : 0<ell) (c : ℝ) (hc : 0<c)
    (t : ℝ) (f : EllipticField ell M) (q : HaarNode) :
    HaarHeatIntegrand.kernel (c*ell) (c*M) (mul_pos hc hell) (t,scale c hc f) q=
      Real.sqrt c•HaarHeatIntegrand.kernel ell M hell (t,f) q := by
  rw [HaarHeatIntegrand.kernel_apply,HaarHeatIntegrand.kernel_apply]
  by_cases ht : 0<t
  · simp only [ht,ite_true]
    change heat t (globalHaarColumn q (c•f.1))=Real.sqrt c•heat t (globalHaarColumn q f.1)
    rw [globalHaarColumn_scale_elliptic q f.1 hell f.2.2 hc]
    exact (heat t).map_smul_of_tower (Real.sqrt c) _
  · simp only [ht,ite_false,smul_zero]

/-- Exact infinite Hilbert-column homogeneity, before any stochastic
integration or state approximation. -/
theorem real_kernel_scale {ell M : ℝ} (hell : 0<ell) (c : ℝ) (hc : 0<c)
    (t : ℝ) (f : EllipticField ell M) :
    RealHaarIntegrand.kernel (c*ell) (c*M) (mul_pos hc hell) (t,scale c hc f)=
      Real.sqrt c•RealHaarIntegrand.kernel ell M hell (t,f) := by
  apply lp.ext
  funext q
  change RealHaarIntegrand.kernel _ _ _ _ q=Real.sqrt c•RealHaarIntegrand.kernel _ _ _ _ q
  rw [RealHaarIntegrand.kernel_apply,RealHaarIntegrand.kernel_apply,complex_kernel_scale hell c hc]
  exact (Complex.reCLM.compLpL 2 haarAddCircle).map_smul _ _

theorem scaled_bounds {a : ℝ→ℝ} {ell M c : ℝ} (hc : 0<c)
    (hb : ∀ z,ell≤a z ∧ a z≤M) : ∀ z,c*ell≤c*a z ∧ c*a z≤c*M :=
  fun z => ⟨mul_le_mul_of_nonneg_left (hb z).1 hc.le,mul_le_mul_of_nonneg_left (hb z).2 hc.le⟩

theorem coefficientField_scale {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0<ell)
    (hb : ∀ z,ell≤a z ∧ a z≤M) (c : ℝ) (hc : 0<c) (u : LowBands.StateL2) :
    coefficientField (fun z => c*a z) (ha.const_mul c) (c*ell) (c*M) (mul_pos hc hell)
      (scaled_bounds hc hb) u=scale c hc (coefficientField a ha ell M hell hb u) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [CoefficientFields.coefficient_ae (fun z => c*a z) (ha.const_mul c) (c*M)
      (absBound (mul_pos hc hell) (scaled_bounds hc hb)) u,
    CoefficientFields.coefficient_ae a ha M (absBound hell hb) u,
    Lp.coeFn_smul c (coefficientField a ha ell M hell hb u).1] with x hs hf hx
  change CoefficientFields.coefficient _ _ _ _ u x=(c•(coefficientField a ha ell M hell hb u).1) x
  rw [hs,hx]
  change ((c*a (u x):ℝ):ℂ)=c•CoefficientFields.coefficient a ha M (absBound hell hb) u x
  rw [hf,Complex.real_smul,Complex.ofReal_mul]

end SHE.HaarFieldScaling
