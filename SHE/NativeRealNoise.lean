module

public import SHE.NativeBesselReal
public import SHE.ActualJointPredictable

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.NativeRealNoise
open Set MeasureTheory Real AddCircle StoppedFourier FiniteHaar NativeRandomKernel
  DyadicApproximation
open scoped ENNReal NNReal
local instance nativeRealNoise_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeRealNoise_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance nativeRealNoise_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nativeRealNoise_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeRealNoise_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance nativeRealNoise_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance nativeRealNoise_realMeasurable : MeasurableSpace RealL2 := borel RealL2
local instance nativeRealNoise_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeRealNoise_columnsMeasurable : MeasurableSpace SignedKernelColumns.Space := borel SignedKernelColumns.Space
local instance nativeRealNoise_columnsBorel : BorelSpace SignedKernelColumns.Space := ⟨rfl⟩
local instance nativeRealNoise_realColumnsMeasurable : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance nativeRealNoise_realColumnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {X : Type} [MeasurableSpace X]

theorem integralOperator_section (F : X × (HeatCircle × HeatCircle) → ℂ) (x : X) :
    integralOperator F x=integralOperator (fun z : Unit × (HeatCircle × HeatCircle) => F (x,z.2)) () := rfl

/-- The literal scalar kernel operator preserves real fields. Only a
finite bound on each parameter section is required. -/
theorem integralOperator_real {F : X × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    (hb : ∀ x,∃ B : ℝ,0 ≤ B ∧ ∀ y z,‖F (x,(y,z))‖ ≤ B)
    (hr : ∀ x y z,(F (x,(y,z))).im=0) (x : X) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle,(v y).im=0) :
    ∀ᵐ y ∂haarAddCircle,(integralOperator F x v y).im=0 := by
  obtain ⟨B,hB,hbound⟩ := hb x
  let G : Unit × (HeatCircle × HeatCircle) → ℂ := fun z => F (x,z.2)
  have hG : Measurable G := hF.comp (measurable_const.prodMk measurable_snd)
  have hGb (_ : Unit) (y z : HeatCircle) : ‖G ((),(y,z))‖ ≤ B := hbound y z
  rw [integralOperator_section F x]
  filter_upwards [integralOperator_ae hG hB hGb () v] with z hz
  rw [hz]
  have hvInt : Integrable (v : HeatCircle → ℂ) haarAddCircle :=
    (Lp.memLp v).integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hm : AEStronglyMeasurable (fun y : HeatCircle => G ((),(y,z))) haarAddCircle :=
    (hG.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hi : Integrable (fun y : HeatCircle => G ((),(y,z))*v y) haarAddCircle :=
    hvInt.bdd_mul hm (ae_of_all _ (fun y => hbound y z))
  have hI := integral_im hi
  change (∫ y : HeatCircle,(G ((),(y,z))*v y).im ∂haarAddCircle)=
    (∫ y : HeatCircle,G ((),(y,z))*v y ∂haarAddCircle).im at hI
  rw [←hI]
  apply integral_eq_zero_of_ae
  filter_upwards [hv] with y hy
  change (F (x,(y,z))*v y).im=0
  simp only [Complex.mul_im,hr,hy,mul_zero,zero_mul,add_zero]

def columnsPart : SignedKernelColumns.Space →L[ℝ] RealHaarIntegrand.Columns :=
  HilbertColumns.mapCLM NativeBesselReal.part

def columnsEmbed : RealHaarIntegrand.Columns →L[ℝ] SignedKernelColumns.Space :=
  HilbertColumns.mapCLM NativeHeatObservation.embed

theorem columns_embed_part (v : SignedKernelColumns.Space)
    (hv : ∀ i,∀ᵐ y ∂haarAddCircle,(v i y).im=0) : columnsEmbed (columnsPart v)=v := by
  apply lp.ext
  funext i
  exact NativeBesselReal.embed_part (v i) (hv i)

theorem columns_part_embed (v : RealHaarIntegrand.Columns) : columnsPart (columnsEmbed v)=v := by
  apply lp.ext
  funext i
  exact NativeBesselReal.part_embed (v i)

theorem columnsPart_norm_sq (v : SignedKernelColumns.Space)
    (hv : ∀ i,∀ᵐ y ∂haarAddCircle,(v i y).im=0) : ‖columnsPart v‖^2=‖v‖^2 := by
  rw [HilbertColumns.norm_sq,HilbertColumns.norm_sq]
  exact tsum_congr (fun i => congrArg (fun s : ℝ => s^2) (NativeBesselReal.part_norm (v i) (hv i)))

theorem columnsEmbed_norm_sq (v : RealHaarIntegrand.Columns) : ‖columnsEmbed v‖^2=‖v‖^2 := by
  rw [HilbertColumns.norm_sq,HilbertColumns.norm_sq]
  exact tsum_congr (fun i => congrArg (fun s : ℝ => s^2) (NativeHeatObservation.embed_norm (v i)))

theorem rawColumns_real {F : X × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    (hb : ∀ x,∃ B : ℝ,0 ≤ B ∧ ∀ y z,‖F (x,(y,z))‖ ≤ B)
    (hr : ∀ x y z,(F (x,(y,z))).im=0)
    {Λ ρ ell M : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hell : 0 < ell)
    (c d : X → EllipticField ell M) (x : X) (i : HaarNode) :
    ∀ᵐ y ∂haarAddCircle,(SignedKernelColumns.rawColumns F Λ ρ hΛ hρ ell M hell c d x i y).im=0 := by
  rw [SignedKernelColumns.rawColumns_apply]
  apply NativeBesselReal.bessel_real
  apply integralOperator_real hF hb hr
  apply CircleNormalization.push_ae_property _ (fun z : ℂ => z.im=0)
  filter_upwards [globalHaarColumn_real_ae i (d x).1 (d x).2.1,
    globalHaarColumn_real_ae i (c x).1 (c x).2.1,
    Lp.coeFn_sub (globalHaarColumn i (d x).1) (globalHaarColumn i (c x).1)] with y hd hc hs
  rw [hs]
  change (globalHaarColumn i (d x).1 y-globalHaarColumn i (c x).1 y).im=0
  simp only [Complex.sub_im,hd,hc,sub_self]

/-- These are actual columns in the original real unit-circle Itô
space, with precisely the same countable Haar coordinates. -/
def rawColumns (F : X × (HeatCircle × HeatCircle) → ℂ)
    (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ell M : ℝ) (hell : 0 < ell)
    (c d : X → EllipticField ell M) (x : X) : RealHaarIntegrand.Columns :=
  columnsPart (SignedKernelColumns.rawColumns F Λ ρ hΛ hρ ell M hell c d x)

theorem rawColumns_norm_sq {F : X × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    (hb : ∀ x,∃ B : ℝ,0 ≤ B ∧ ∀ y z,‖F (x,(y,z))‖ ≤ B)
    (hr : ∀ x y z,(F (x,(y,z))).im=0)
    {Λ ρ ell M : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hell : 0 < ell)
    (c d : X → EllipticField ell M) (x : X) :
    ‖rawColumns F Λ ρ hΛ hρ ell M hell c d x‖^2=
      ‖SignedKernelColumns.rawColumns F Λ ρ hΛ hρ ell M hell c d x‖^2 :=
  columnsPart_norm_sq _ (rawColumns_real hF hb hr hΛ hρ hell c d x)

theorem rawColumns_embed {F : X × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    (hb : ∀ x,∃ B : ℝ,0 ≤ B ∧ ∀ y z,‖F (x,(y,z))‖ ≤ B)
    (hr : ∀ x y z,(F (x,(y,z))).im=0)
    {Λ ρ ell M : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hell : 0 < ell)
    (c d : X → EllipticField ell M) (x : X) :
    columnsEmbed (rawColumns F Λ ρ hΛ hρ ell M hell c d x)=
      SignedKernelColumns.rawColumns F Λ ρ hΛ hρ ell M hell c d x :=
  columns_embed_part _ (rawColumns_real hF hb hr hΛ hρ hell c d x)

theorem rawColumns_measurable {F : X × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    (hb : ∀ x,∃ B : ℝ,0 ≤ B ∧ ∀ y z,‖F (x,(y,z))‖ ≤ B)
    {Λ ρ ell M : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hell : 0 < ell)
    (c d : X → EllipticField ell M) (hc : Measurable c) (hd : Measurable d) :
    Measurable (rawColumns F Λ ρ hΛ hρ ell M hell c d) :=
  columnsPart.continuous.measurable.comp (SignedKernelColumns.rawColumns_measurable hF hb hΛ hρ hell c d hc hd)

end SHE.NativeRealNoise
