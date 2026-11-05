module

public import SHE.CanonicalProfile
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
set_option autoImplicit false

/-! Joint scalar fields give actual Borel L²-valued coefficient maps. -/
noncomputable section
namespace SHE.MeasurableL2Field
open Set MeasureTheory StoppedFourier

theorem measurable_of_dist {P E : Type*} [MeasurableSpace P] [PseudoMetricSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : P → E}
    (hf : ∀ y, Measurable (fun p => dist (f p) y)) : Measurable f := by
  apply measurable_of_isOpen
  intro s hs
  let B : Set (Set E) := {b | ∃ y : E, ∃ r : ℝ, b = Metric.ball y r ∧ b ⊆ s}
  have hB : ⋃₀ B = s := by
    apply subset_antisymm
    · exact sUnion_subset (fun b hb => by obtain ⟨y, r, _, hb⟩ := hb; exact hb)
    · intro y hy
      obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs y hy
      exact mem_sUnion.mpr ⟨Metric.ball y r, ⟨y, r, rfl, hrs⟩, Metric.mem_ball_self hr⟩
  obtain ⟨T, hT, hTB, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable B (by
    intro b hb
    obtain ⟨y, r, rfl, _⟩ := hb
    exact Metric.isOpen_ball)
  rw [← hB, ← hTU, preimage_sUnion]
  apply MeasurableSet.biUnion hT
  intro b hb
  obtain ⟨y, r, rfl, _⟩ := hTB hb
  exact measurableSet_lt (hf y) measurable_const

def l2Field {P X : Type*} [MeasurableSpace X] {ν : Measure X}
    (F : P × X → ℂ) (hF : ∀ p, MemLp (fun x => F (p, x)) 2 ν) (p : P) : Lp ℂ 2 ν :=
  (hF p).toLp (fun x => F (p, x))

theorem l2Field_dist {P X : Type*} [MeasurableSpace X] {ν : Measure X}
    (F : P × X → ℂ) (hF : ∀ p, MemLp (fun x => F (p, x)) 2 ν) (p : P) (g : Lp ℂ 2 ν) :
    dist (l2Field F hF p) g = Real.sqrt (∫ x, ‖F (p, x) - g x‖ ^ 2 ∂ν) := by
  have he : ‖l2Field F hF p - g‖ ^ 2 = ∫ x, ‖F (p, x) - g x‖ ^ 2 ∂ν := by
    rw [L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (l2Field F hF p) g, (hF p).coeFn_toLp] with x hx hy
    rw [hx, Pi.sub_apply]
    change ‖(hF p).toLp (fun x => F (p, x)) x - g x‖ ^ 2 = _
    rw [hy]
  rw [dist_eq_norm, ← he, Real.sqrt_sq (norm_nonneg _)]

/-- Joint measurability and genuine section integrability imply Borel
measurability into the actual separable spatial L² space. -/
theorem l2Field_measurable {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    {ν : Measure X} [SFinite ν] [SecondCountableTopology (Lp ℂ 2 ν)]
    [MeasurableSpace (Lp ℂ 2 ν)] [BorelSpace (Lp ℂ 2 ν)]
    {F : P × X → ℂ} (hF : Measurable F) (hsections : ∀ p, MemLp (fun x => F (p, x)) 2 ν) :
    Measurable (l2Field F hsections) := by
  apply measurable_of_dist
  intro g
  have hm : Measurable (fun p : P × X => ‖F p - g p.2‖ ^ 2) :=
    (hF.sub ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)).norm.pow_const (2 : ℕ)
  have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable.sqrt
  convert hi using 1
  funext p
  exact l2Field_dist F hsections p g

/-- Total canonical L² realization, using zero only outside its true
integrability domain. Under the proved profile bounds the first branch
always applies. -/
def realizeL2 {P X : Type*} [MeasurableSpace X] {ν : Measure X}
    (F : P × X → ℂ) (p : P) : Lp ℂ 2 ν := by
  classical
  exact if h : MemLp (fun x => F (p, x)) 2 ν then h.toLp (fun x => F (p, x)) else 0

theorem realizeL2_eq {P X : Type*} [MeasurableSpace X] {ν : Measure X}
    (F : P × X → ℂ) (hsections : ∀ p, MemLp (fun x => F (p, x)) 2 ν) :
    realizeL2 (ν := ν) F = l2Field F hsections := by
  funext p
  simp only [realizeL2, dite_eq_left (hsections p), l2Field]

theorem realizeL2_ae {P X : Type*} [MeasurableSpace X] {ν : Measure X}
    (F : P × X → ℂ) (hsections : ∀ p, MemLp (fun x => F (p, x)) 2 ν) (p : P) :
    realizeL2 (ν := ν) F p =ᵐ[ν] (fun x => F (p, x)) := by
  rw [realizeL2_eq F hsections]
  exact (hsections p).coeFn_toLp

theorem realizeL2_measurable {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    {ν : Measure X} [SFinite ν] [SecondCountableTopology (Lp ℂ 2 ν)]
    [MeasurableSpace (Lp ℂ 2 ν)] [BorelSpace (Lp ℂ 2 ν)]
    {F : P × X → ℂ} (hF : Measurable F) (hsections : ∀ p, MemLp (fun x => F (p, x)) 2 ν) :
    Measurable (realizeL2 (ν := ν) F) := by
  rw [realizeL2_eq F hsections]
  exact l2Field_measurable hF hsections

theorem real_l2_diff_norm {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} {F G : Lp ℂ 2 ν}
    (hF : (F : X → ℂ) =ᵐ[ν] (fun x => (f x : ℂ)))
    (hG : (G : X → ℂ) =ᵐ[ν] (fun x => (g x : ℂ))) :
    ‖F - G‖ = ProfileL2.normTwo ν (fun x => f x - g x) := by
  have he : ‖F - G‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂ν := by
    rw [L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub F G, hF, hG] with x hx hy hz
    rw [hx, Pi.sub_apply, hy, hz, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  apply (sq_eq_sq₀ (norm_nonneg _) (ProfileL2.normTwo_nonneg _ _)).mp
  rw [he, ProfileL2.normTwo_sq]

end SHE.MeasurableL2Field
