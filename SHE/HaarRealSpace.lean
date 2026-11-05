module

public import SHE.HaarReal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open MeasureTheory AddCircle CircleHeat
open scoped ENNReal
local instance haarRealSpace_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem isClosed_realInputSpace : IsClosed (realInputSpace : Set HaarInput) := by
  rw [realInputSpace, Submodule.coe_iInf]
  exact isClosed_iInter (fun q =>
    (Complex.imCLM.comp (lp.evalCLM ℝ (fun _ : HaarNode => ℂ) 2 q)).isClosed_ker)

instance haarRealSpace_physicalComplete : CompleteSpace realCircleSpace :=
  isClosed_realCircleSpace.completeSpace_coe

instance haarRealSpace_inputComplete : CompleteSpace realInputSpace :=
  isClosed_realInputSpace.completeSpace_coe

theorem realEmbed_norm_eq (v : DyadicApproximation.RealL2) :
    ‖DyadicApproximation.realEmbed v‖ = ‖v‖ := by
  apply le_antisymm (DyadicApproximation.realEmbed_norm_le v)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [DyadicApproximation.realEmbed_ae v] with y hy
  rw [hy, Complex.norm_real]

/-- Literal real `L²` is identified with the closed real-valued subspace
of the complex Fourier realization, with its exact norm. -/
def realCircleIdentification : DyadicApproximation.RealL2 ≃ₗᵢ[ℝ] realCircleSpace where
  toFun v := ⟨DyadicApproximation.realEmbed v, (mem_realCircleSpace _).mpr (by
    filter_upwards [DyadicApproximation.realEmbed_ae v] with y hy
    rw [hy]
    exact Complex.ofReal_im _)⟩
  invFun v := DyadicApproximation.realPart v.1
  left_inv v := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLp (DyadicApproximation.realEmbed v),
      DyadicApproximation.realEmbed_ae v] with y hr he
    change DyadicApproximation.realPart (DyadicApproximation.realEmbed v) y =
      (DyadicApproximation.realEmbed v y).re at hr
    rw [hr, he, Complex.ofReal_re]
  right_inv v := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [DyadicApproximation.realEmbed_ae (DyadicApproximation.realPart v.1),
      Complex.reCLM.coeFn_compLp v.1, (mem_realCircleSpace v.1).mp v.2] with y he hr hi
    rw [he]
    change DyadicApproximation.realPart v.1 y = (v.1 y).re at hr
    rw [hr]
    exact Complex.ext (by simp) (by simpa using hi.symm)
  map_add' v w := Subtype.ext (map_add DyadicApproximation.realEmbed v w)
  map_smul' r v := Subtype.ext (map_smul DyadicApproximation.realEmbed r v)
  norm_map' v := realEmbed_norm_eq v

abbrev RealHaarInput := lp (fun _ : HaarNode => ℝ) 2

def realInputEmbed (x : RealHaarInput) : HaarInput :=
  ⟨fun q => (x q : ℂ), (lp.memℓp x).mono' (fun q => by simp)⟩

def realInputPart (x : HaarInput) : RealHaarInput :=
  ⟨fun q => (x q).re, (lp.memℓp x).mono' (fun q => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (x q))⟩

theorem realInputEmbed_norm_eq (x : RealHaarInput) : ‖realInputEmbed x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  congr 1
  apply tsum_congr
  intro q
  change ‖(x q : ℂ)‖ ^ _ = _
  rw [Complex.norm_real]

/-- Literal real square-summable Haar coordinates are identified with
the closed real-coordinate subspace of the complex common input. -/
def realInputIdentification : RealHaarInput ≃ₗᵢ[ℝ] realInputSpace where
  toFun x := ⟨realInputEmbed x, (mem_realInputSpace _).mpr (fun q => Complex.ofReal_im _)⟩
  invFun x := realInputPart x.1
  left_inv x := by
    apply lp.ext
    funext q
    exact Complex.ofReal_re _
  right_inv x := by
    apply Subtype.ext
    apply lp.ext
    funext q
    apply Complex.ext
    · rfl
    · exact ((mem_realInputSpace x.1).mp x.2 q).symm
  map_add' x y := by
    apply Subtype.ext
    apply lp.ext
    funext q
    exact Complex.ofReal_add _ _
  map_smul' r x := by
    apply Subtype.ext
    apply lp.ext
    funext q
    exact Complex.ofReal_mul _ _
  norm_map' := realInputEmbed_norm_eq

/-- The actual innovation rotation on the literal real physical and
real coordinate Hilbert spaces used for cylindrical Brownian motion. -/
def realPhysicalInnovation (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    DyadicApproximation.RealL2 ≃ₗᵢ[ℝ] RealHaarInput :=
  (realCircleIdentification.trans (realInnovationRotation f m U hm hfreal hfbound)).trans
    realInputIdentification.symm

local instance haarRealSpace_exponentFinite : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance haarRealSpace_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance haarRealSpace_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance haarRealSpace_realCircleSigma : MeasurableSpace DyadicApproximation.RealL2 := borel _
local instance haarRealSpace_realCircleBorel : BorelSpace DyadicApproximation.RealL2 := ⟨rfl⟩
local instance haarRealSpace_realInputSigma : MeasurableSpace RealHaarInput := borel _
local instance haarRealSpace_realInputBorel : BorelSpace RealHaarInput := ⟨rfl⟩

def fieldRealInnovation (m U : ℝ) (hm : 0 < m) (f : EllipticField m U) :
    DyadicApproximation.RealL2 ≃ₗᵢ[ℝ] RealHaarInput :=
  realPhysicalInnovation f.1 m U hm f.2.1 f.2.2

theorem continuous_fieldRealInnovation_joint (m U : ℝ) (hm : 0 < m) :
    Continuous (fun p : EllipticField m U × DyadicApproximation.RealL2 =>
      fieldRealInnovation m U hm p.1 p.2) := by
  have hc := (continuous_fieldInnovation_joint m U hm).comp
    (continuous_fst.prodMk (DyadicApproximation.realEmbed.continuous.comp continuous_snd))
  have hs : Continuous (fun p : EllipticField m U × DyadicApproximation.RealL2 =>
      realInnovationRotation p.1.1 m U hm p.1.2.1 p.1.2.2 (realCircleIdentification p.2)) :=
    hc.subtype_mk _
  exact realInputIdentification.symm.continuous.comp hs

theorem measurable_fieldRealInnovation_joint (m U : ℝ) (hm : 0 < m) :
    Measurable (fun p : EllipticField m U × DyadicApproximation.RealL2 =>
      fieldRealInnovation m U hm p.1 p.2) :=
  (continuous_fieldRealInnovation_joint m U hm).measurable

/-- This works for any sigma algebra, in particular the predictable
sigma algebra of a supplied filtration. -/
theorem measurable_fieldRealInnovation_process {X : Type*} [MeasurableSpace X]
    (m U : ℝ) (hm : 0 < m) (f : X → EllipticField m U) (hf : Measurable f)
    (v : X → DyadicApproximation.RealL2) (hv : Measurable v) :
    Measurable (fun p => fieldRealInnovation m U hm (f p) (v p)) := by
  let g : X → EllipticField m U × DyadicApproximation.RealL2 := fun p => (f p, v p)
  have hg : Measurable g := hf.prodMk hv
  change Measurable ((fun p : EllipticField m U × DyadicApproximation.RealL2 =>
    fieldRealInnovation m U hm p.1 p.2) ∘ g)
  exact (measurable_fieldRealInnovation_joint m U hm).comp hg

end SHE.FiniteHaar
