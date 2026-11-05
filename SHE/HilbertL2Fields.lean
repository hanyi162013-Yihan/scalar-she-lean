module

public import SHE.MeasurableL2Field

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HilbertL2Fields
open MeasureTheory
open scoped ENNReal

variable {P X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ν : Measure X}

/-- The true square-integrable section of a Hilbert-valued spatial field. -/
def field (F : P × X → E) (hF : ∀ p, MemLp (fun x => F (p,x)) 2 ν)
    (p : P) : Lp E 2 ν := (hF p).toLp (fun x => F (p,x))

theorem field_ae (F : P × X → E) (hF : ∀ p, MemLp (fun x => F (p,x)) 2 ν)
    (p : P) : (field F hF p : X → E) =ᵐ[ν] fun x => F (p,x) :=
  (hF p).coeFn_toLp

theorem field_norm_sq (F : P × X → E) (hF : ∀ p, MemLp (fun x => F (p,x)) 2 ν)
    (p : P) : ‖field F hF p‖^2 = ∫ x, ‖F (p,x)‖^2 ∂ν := by
  rw [StoppedFourier.L2_norm_sq_eq_integral]
  exact integral_congr_ae ((field_ae F hF p).mono (fun x hx => by
    change ‖field F hF p x‖^2=‖F (p,x)‖^2
    change field F hF p x=F (p,x) at hx
    rw [hx]))

theorem field_dist (F : P × X → E) (hF : ∀ p, MemLp (fun x => F (p,x)) 2 ν)
    (p : P) (g : Lp E 2 ν) :
    dist (field F hF p) g = Real.sqrt (∫ x, ‖F (p,x)-g x‖^2 ∂ν) := by
  have he : ‖field F hF p-g‖^2 = ∫ x, ‖F (p,x)-g x‖^2 ∂ν := by
    rw [StoppedFourier.L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (field F hF p) g,field_ae F hF p] with x hx hy
    rw [hx,Pi.sub_apply,hy]
  rw [dist_eq_norm,← he,Real.sqrt_sq (norm_nonneg _)]

/-- Joint Borel representatives yield an actual Borel map into spatial L²,
also when the values of the field are themselves an infinite-dimensional
Hilbert space. -/
theorem field_measurable [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    [MeasurableSpace (Lp E 2 ν)] [BorelSpace (Lp E 2 ν)]
    {F : P × X → E} (hF : Measurable F)
    (hsections : ∀ p, MemLp (fun x => F (p,x)) 2 ν) :
    Measurable (field F hsections) := by
  apply MeasurableL2Field.measurable_of_dist
  intro g
  have hm : Measurable (fun p : P × X => ‖F p-g p.2‖^2) :=
    (hF.sub ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)).norm.pow_const (2:ℕ)
  have hi := (hm.stronglyMeasurable.integral_prod_right' (ν:=ν)).measurable.sqrt
  convert hi using 1
  funext p
  exact field_dist F hsections p g

/-- Canonical total realization; under the section bounds its true L²
branch applies everywhere. -/
def realize (F : P × X → E) (p : P) : Lp E 2 ν := by
  classical
  exact if h : MemLp (fun x => F (p,x)) 2 ν then h.toLp (fun x => F (p,x)) else 0

theorem realize_eq (F : P × X → E) (hF : ∀ p, MemLp (fun x => F (p,x)) 2 ν) :
    realize (ν:=ν) F = field F hF := by
  funext p
  simp only [realize,dite_eq_left (hF p),field]

theorem realize_ae (F : P × X → E) (hF : ∀ p, MemLp (fun x => F (p,x)) 2 ν)
    (p : P) : (realize (ν:=ν) F p : X → E) =ᵐ[ν] fun x => F (p,x) := by
  rw [realize_eq F hF]
  exact field_ae F hF p

theorem realize_measurable [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    [MeasurableSpace (Lp E 2 ν)] [BorelSpace (Lp E 2 ν)]
    {F : P × X → E} (hF : Measurable F)
    (hsections : ∀ p, MemLp (fun x => F (p,x)) 2 ν) :
    Measurable (realize (ν:=ν) F) := by
  rw [realize_eq F hsections]
  exact field_measurable hF hsections

theorem realize_norm_sq (F : P × X → E) (hF : ∀ p, MemLp (fun x => F (p,x)) 2 ν)
    (p : P) : ‖realize (ν:=ν) F p‖^2 = ∫ x, ‖F (p,x)‖^2 ∂ν := by
  rw [realize_eq F hF]
  exact field_norm_sq F hF p

/-- A coarse uniform bound supplies all Fubini applicability. The sharp
expected section estimate is then integrated without changing its constant. -/
theorem expected_norm_sq_bound [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure P) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {F : P × X → E} (hF : Measurable F)
    {B A : ℝ} (hb : ∀ p x, ‖F (p,x)‖ ≤ B)
    (hsharp : ∀ x, (∫ p, ‖F (p,x)‖^2 ∂μ) ≤ A) :
    Integrable (fun p => ‖realize (ν:=ν) F p‖^2) μ ∧
      (∫ p, ‖realize (ν:=ν) F p‖^2 ∂μ) ≤ A := by
  have hs (p : P) : MemLp (fun x => F (p,x)) 2 ν :=
    MemLp.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
      (ae_of_all _ (hb p))
  have hp : Integrable (fun p : P × X => ‖F p‖^2) (μ.prod ν) := by
    apply (integrable_const (B^2)).mono' (hF.norm.pow_const (2:ℕ)).aestronglyMeasurable
    exact ae_of_all _ (fun p => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb p.1 p.2) 2)
  have he : (fun p => ‖realize (ν:=ν) F p‖^2) =
      (fun p => ∫ x, ‖F (p,x)‖^2 ∂ν) := funext (realize_norm_sq F hs)
  refine ⟨by rw [he]; exact hp.integral_prod_left,?_⟩
  rw [he,integral_integral_swap hp]
  exact (integral_mono hp.integral_prod_right (integrable_const A) hsharp).trans_eq (by simp)

end SHE.HilbertL2Fields
