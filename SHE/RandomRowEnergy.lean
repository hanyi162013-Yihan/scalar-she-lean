module

public import SHE.GaussianNegativePacket
public import SHE.MeasurableL2Field
public import SHE.ProfileL2

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RandomRowEnergy
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real CircleHeat HeatMarkov
open scoped BigOperators ENNReal
local instance randomRowEnergy_periodPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance randomRowEnergy_exponentFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance randomRowEnergy_measurableSpace : MeasurableSpace CircleL2 := borel CircleL2
local instance randomRowEnergy_borelSpace : BorelSpace CircleL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The actual spatial L² row obtained from its jointly measurable scalar
representative. The coarse bound below ensures this is always its true
L² realization. -/
def row (F : Ω × UnitAddCircle → ℂ) (ω : Ω) : CircleL2 :=
  MeasurableL2Field.realizeL2 (ν:=haarAddCircle) F ω

def rms (F : Ω × UnitAddCircle → ℂ) (x : UnitAddCircle) : ℝ :=
  ProfileL2.normTwo μ (fun ω => ‖F (ω,x)‖)

theorem section_memLp {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) (ω : Ω) :
    MemLp (fun x => F (ω,x)) 2 haarAddCircle :=
  MemLp.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
    (ae_of_all _ (hb ω))

theorem row_ae {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) (ω : Ω) :
    (row F ω : UnitAddCircle → ℂ)=ᵐ[haarAddCircle] fun x => F (ω,x) :=
  MeasurableL2Field.realizeL2_ae F (section_memLp hF hb) ω

theorem row_measurable {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) : Measurable (row F) :=
  MeasurableL2Field.realizeL2_measurable hF (section_memLp hF hb)

theorem rms_nonneg (F : Ω × UnitAddCircle → ℂ) (x : UnitAddCircle) : 0 ≤ rms μ F x :=
  ProfileL2.normTwo_nonneg μ _

theorem rms_measurable {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F) : Measurable (rms μ F) := by
  exact (hF.norm.pow_const (2:ℕ)).stronglyMeasurable.integral_prod_left'.measurable.sqrt

theorem rms_bound {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) (x : UnitAddCircle) : rms μ F x ≤ B := by
  apply ProfileL2.normTwo_bound ((hF.comp (measurable_id.prodMk measurable_const)).norm) hB
  intro ω
  change |‖F (ω,x)‖| ≤ B
  rw [abs_of_nonneg (norm_nonneg _)]
  exact hb ω x

theorem rms_memLp {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) :
    MemLp (fun x => (rms μ F x : ℂ)) 2 haarAddCircle := by
  apply MemLp.of_bound (Complex.continuous_ofReal.measurable.comp (rms_measurable μ hF)).aestronglyMeasurable B
  exact ae_of_all _ (fun x => by
    change ‖(rms μ F x : ℂ)‖ ≤ B
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (rms_nonneg μ F x)]
    exact rms_bound μ hF hB hb x)

def rmsRow (F : Ω × UnitAddCircle → ℂ) : CircleL2 :=
  MeasurableL2Field.realizeL2 (ν:=haarAddCircle) (fun p : Unit × UnitAddCircle => (rms μ F p.2 : ℂ)) ()

theorem rmsRow_ae {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) :
    (rmsRow μ F : UnitAddCircle → ℂ)=ᵐ[haarAddCircle] fun x => (rms μ F x : ℂ) :=
  MeasurableL2Field.realizeL2_ae _ (fun _ => rms_memLp μ hF hB hb) ()

theorem row_norm_sq {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) (ω : Ω) :
    ‖row F ω‖^2=∫ x, ‖F (ω,x)‖^2 ∂haarAddCircle := by
  rw [StoppedFourier.L2_norm_sq_eq_integral]
  exact integral_congr_ae ((row_ae hF hb ω).mono (fun x hx => by
    change ‖row F ω x‖^2=‖F (ω,x)‖^2
    change row F ω x=F (ω,x) at hx
    rw [hx]))

theorem row_normOne {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) (ω : Ω) :
    normOne (row F ω)=∫ x, ‖F (ω,x)‖ ∂haarAddCircle :=
  integral_congr_ae ((row_ae hF hb ω).mono (fun x hx => by
    change ‖row F ω x‖=‖F (ω,x)‖
    change row F ω x=F (ω,x) at hx
    rw [hx]))

/-- Genuine Fubini identity for the expected spatial row energy. The
coarse bound is used only for integrability; the exact RMS field is kept. -/
theorem expected_norm_sq {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) :
    Integrable (fun ω => ‖row F ω‖^2) μ ∧
      (∫ ω, ‖row F ω‖^2 ∂μ)=‖rmsRow μ F‖^2 := by
  have hprod : Integrable (fun p : Ω × UnitAddCircle => ‖F p‖^2) (μ.prod haarAddCircle) := by
    apply (integrable_const (B^2)).mono' (hF.norm.pow_const (2:ℕ)).aestronglyMeasurable
    exact ae_of_all _ (fun p => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb p.1 p.2) 2)
  have hnorm : (fun ω => ‖row F ω‖^2)=(fun ω => ∫ x, ‖F (ω,x)‖^2 ∂haarAddCircle) :=
    funext (row_norm_sq hF hb)
  refine ⟨by rw [hnorm]; exact hprod.integral_prod_left,?_⟩
  rw [hnorm,integral_integral_swap hprod,StoppedFourier.L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [rmsRow_ae μ hF hB hb] with x hx
  rw [hx,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (rms_nonneg μ F x)]
  exact (ProfileL2.normTwo_sq μ (fun ω => ‖F (ω,x)‖)).symm

/-- Minkowski preserves the sole sharp RMS envelope: expected squared
spatial L¹ mass is bounded by the L¹ mass of the actual RMS field. -/
theorem expected_normOne_sq {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) :
    Integrable (fun ω => normOne (row F ω)^2) μ ∧
      (∫ ω, normOne (row F ω)^2 ∂μ) ≤ normOne (rmsRow μ F)^2 := by
  have hg : Integrable (rms μ F) haarAddCircle :=
    ((ProfileL2.bounded_memLp (rms_measurable μ hF)
      (fun x => by rw [abs_of_nonneg (rms_nonneg μ F x)]; exact rms_bound μ hF hB hb x)).integrable (by norm_num))
  have hm : Measurable (fun ω => normOne (row F ω)) := by
    have he : (fun ω => normOne (row F ω))=(fun ω => ∫ x, ‖F (ω,x)‖ ∂haarAddCircle) :=
      funext (row_normOne hF hb)
    rw [he]
    exact hF.norm.stronglyMeasurable.integral_prod_right'.measurable
  have hmass (ω : Ω) : normOne (row F ω) ≤ B := by
    rw [row_normOne hF hb]
    exact (integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
      (integrable_const B) (ae_of_all _ (hb ω))).trans_eq (by simp)
  have hInt : Integrable (fun ω => normOne (row F ω)^2) μ := by
    apply (integrable_const (B^2)).mono' (hm.pow_const (2:ℕ)).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (normOne_nonneg _) (hmass ω) 2)
  have hM := ProfileL2.bounded_minkowski_two (μ:=haarAddCircle) (ν:=μ)
    (F:=fun p : UnitAddCircle × Ω => ‖F (p.2,p.1)‖)
    (a:=rms μ F) (b:=fun _ => B)
    (hF.comp measurable_swap |>.norm) hg (integrable_const B)
    (ae_of_all _ (rms_nonneg μ F)) (ae_of_all _ (fun _ => hB))
    (ae_of_all _ (fun x ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hb ω x))
    (ae_of_all _ (fun _ => le_rfl))
  have he : normOne (rmsRow μ F)=∫ x, rms μ F x ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [rmsRow_ae μ hF hB hb] with x hx
    rw [hx,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (rms_nonneg μ F x)]
  have hM' : Real.sqrt (∫ ω, normOne (row F ω)^2 ∂μ) ≤ normOne (rmsRow μ F) := by
    rw [he]
    simpa only [ProfileL2.normTwo,← row_normOne hF hb] using hM
  refine ⟨hInt,?_⟩
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg (∫ ω, normOne (row F ω)^2 ∂μ)) hM' 2
  rwa [Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg (normOne (row F ω))))] at hh

end SHE.RandomRowEnergy
