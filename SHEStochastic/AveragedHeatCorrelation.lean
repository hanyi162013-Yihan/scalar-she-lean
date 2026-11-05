module

public import SHEStochastic.NativeHeatTranslation
public import SHEStochastic.NativeBesselHeatCap
public import SHE.NativeBesselFieldAE

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.AveragedHeatCorrelation
open MeasureTheory SHE SHE.StoppedFourier AddCircle
open scoped ENNReal
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
variable {Ω : Type*} [MeasurableSpace Ω]
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleL2 :=
  (fourierBasis (T := 2*Real.pi)).repr.toHomeomorph.secondCountableTopology

/-- A uniform bound on the signed, commonly translated correlation
controls the genuine heat energy. Positivity and unit mass belong to
the heat kernel alone; the coefficient profile retains its signs. -/
theorem heat (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → CircleL2) (F : Ω×HeatCircle → ℝ) (hF : Measurable F)
    (hRep : ∀ ω,(f ω : HeatCircle → ℂ)=ᵐ[ν] fun x => (F (ω,x) : ℂ))
    {M C : ℝ} (hM : 0 ≤ M) (hBound : ∀ ω x,|F (ω,x)| ≤ M)
    (hCorr : ∀ x y : HeatCircle,
      |∫ r : HeatCircle×Ω,F (r.2,x+r.1)*F (r.2,y+r.1) ∂(ν).prod μ| ≤ C)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => ‖circleHeatOperator (t/2) (by positivity) (f ω)‖^2) μ ∧
      (∫ ω,‖circleHeatOperator (t/2) (by positivity) (f ω)‖^2 ∂μ) ≤ C := by
  let K := NativeHeatQuadratic.K t ht
  let B := 1+heatConstant*(t/2)^(-(1/2 : ℝ))
  let Q := fun ω => ‖circleHeatOperator (t/2) (by positivity) (f ω)‖^2
  let H : (HeatCircle×Ω)×(HeatCircle×HeatCircle) → ℝ := fun p =>
    K p.2*F (p.1.2,p.2.1+p.1.1)*F (p.1.2,p.2.2+p.1.1)
  have hB : 0 ≤ B := by dsimp only [B];positivity [heatConstant_pos]
  have hK0 (p : HeatCircle×HeatCircle) : 0 ≤ K p := norm_nonneg _
  have hKb (p : HeatCircle×HeatCircle) : K p ≤ B := NativeHeatQuadratic.K_bound ht p
  have hKm : Measurable K := NativeHeatQuadratic.measurable_K ht
  have hHm : Measurable H :=
    ((hKm.comp measurable_snd).mul (hF.comp
      (measurable_fst.snd.prodMk (measurable_snd.fst.add measurable_fst.fst)))).mul
      (hF.comp (measurable_fst.snd.prodMk (measurable_snd.snd.add measurable_fst.fst)))
  have hHb (p : (HeatCircle×Ω)×(HeatCircle×HeatCircle)) : ‖H p‖ ≤ B*M*M := by
    dsimp only [H]
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (hK0 _)]
    exact mul_le_mul (mul_le_mul (hKb _) (hBound _ _) (abs_nonneg _) hB)
      (hBound _ _) (abs_nonneg _) (mul_nonneg hB hM)
  have hHi : Integrable H (((ν).prod μ).prod ((ν).prod ν)) :=
    Integrable.of_bound hHm.aestronglyMeasurable (B*M*M) (ae_of_all _ hHb)
  have hSec (r : HeatCircle×Ω) : Integrable (fun p => H (r,p)) ((ν).prod ν) :=
    Integrable.of_bound (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (B*M*M) (ae_of_all _ (fun p => hHb (r,p)))
  have hQuad (r : HeatCircle×Ω) : (∫ p,H (r,p) ∂(ν).prod ν)=Q r.2 := by
    rw [integral_prod _ (hSec r)]
    exact (NativeHeatTranslation.quadratic ht r.1 (f r.2) (fun x => F (r.2,x)) (hRep r.2)).symm
  have hQiProd : Integrable (fun r : HeatCircle×Ω => Q r.2) ((ν).prod μ) :=
    hHi.integral_prod_left.congr (ae_of_all _ hQuad)
  have hQi : Integrable Q μ := hQiProd.of_comp_snd (NeZero.ne _)
  have hKi : Integrable K ((ν).prod ν) :=
    Integrable.of_bound hKm.aestronglyMeasurable B
      (ae_of_all _ (fun p => by rw [Real.norm_of_nonneg (hK0 p)];exact hKb p))
  have hMass : (∫ p,K p ∂(ν).prod ν)=1 := by
    rw [integral_prod _ hKi]
    simp only [K,NativeHeatQuadratic.K_row ht,integral_const,probReal_univ,one_smul]
  have hCorrBound (p : HeatCircle×HeatCircle) : (∫ r,H (r,p) ∂(ν).prod μ) ≤ K p*C := by
    have he : (fun r => H (r,p))=fun r : HeatCircle×Ω =>
        K p*(F (r.2,p.1+r.1)*F (r.2,p.2+r.1)) := by funext r;dsimp only [H];ring
    rw [he,integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hCorr p.1 p.2)) (hK0 p)
  refine ⟨hQi,?_⟩
  change (∫ ω,Q ω ∂μ) ≤ C
  calc
    _ = ∫ r : HeatCircle×Ω,Q r.2 ∂(ν).prod μ := by
      rw [integral_prod _ hQiProd]
      simp only [integral_const,probReal_univ,one_smul]
    _ = ∫ r,∫ p,H (r,p) ∂(ν).prod ν ∂(ν).prod μ :=
      integral_congr_ae (ae_of_all _ (fun r => (hQuad r).symm))
    _ = ∫ p,∫ r,H (r,p) ∂(ν).prod μ ∂(ν).prod ν := integral_integral_swap hHi
    _ ≤ ∫ p,K p*C ∂(ν).prod ν :=
      integral_mono_ae hHi.integral_prod_right (hKi.mul_const C) (ae_of_all _ hCorrBound)
    _ = C := by rw [integral_mul_const,hMass,one_mul]

/-- The signed averaged correlation controls the actual massive
negative profile energy, with no boundedness assumption on a Bessel
kernel and no spatial frequency truncation. -/
theorem bessel (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → CircleL2) (hf : Measurable f) (F : Ω×HeatCircle → ℝ) (hF : Measurable F)
    (hRep : ∀ ω,(f ω : HeatCircle → ℂ)=ᵐ[ν] fun x => (F (ω,x) : ℂ))
    {M C Λ ρ : ℝ} (hM : 0 ≤ M) (hBound : ∀ ω x,|F (ω,x)| ≤ M) (hC : 0 ≤ C)
    (hCorr : ∀ x y : HeatCircle,
      |∫ r : HeatCircle×Ω,F (r.2,x+r.1)*F (r.2,y+r.1) ∂(ν).prod μ| ≤ C)
    (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) :
    Integrable (fun ω => ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2 ∂μ) ≤ Λ^(-ρ)*C := by
  apply NativeBesselHeatCap.integral_bound μ f hf hΛ hρ hC
  intro t ht
  have hh := heat μ f F hF hRep hM hBound hCorr ht
  rw [← ofReal_integral_eq_lintegral_ofReal hh.1 (ae_of_all _ (fun ω => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hh.2

/-- Bounded joint scalar profiles supply their own Borel spatial L2
realization. The correlation estimate therefore controls the actual
canonical negative profile, without an L2-version hypothesis. -/
theorem field (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω×HeatCircle → ℝ) (hF : Measurable F)
    {M C Λ ρ : ℝ} (hM : 0 ≤ M) (hBound : ∀ ω x,|F (ω,x)| ≤ M) (hC : 0 ≤ C)
    (hCorr : ∀ x y : HeatCircle,
      |∫ r : HeatCircle×Ω,F (r.2,x+r.1)*F (r.2,y+r.1) ∂(ν).prod μ| ≤ C)
    (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) :
    Integrable (fun ω => ‖NativeBesselFieldAE.value Λ ρ hΛ hρ.le (fun p => (F p : ℂ)) ω‖^2) μ ∧
      (∫ ω,‖NativeBesselFieldAE.value Λ ρ hΛ hρ.le (fun p => (F p : ℂ)) ω‖^2 ∂μ) ≤ Λ^(-ρ)*C := by
  let Fc : Ω×HeatCircle → ℂ := fun p => (F p : ℂ)
  have hFc : Measurable Fc := Complex.continuous_ofReal.measurable.comp hF
  have hSec (ω : Ω) : MemLp (fun x => Fc (ω,x)) 2 ν :=
    MemLp.of_bound (hFc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
      (ae_of_all _ (fun x => by simpa only [Fc,Complex.norm_real,Real.norm_eq_abs] using hBound ω x))
  have hm : Measurable (MeasurableL2FieldAE.realization ν Fc) :=
    MeasurableL2FieldAE.realization_measurable ν Fc hFc
  have hRep (ω : Ω) : (MeasurableL2FieldAE.realization ν Fc ω : HeatCircle → ℂ)=ᵐ[ν]
      fun x => (F (ω,x) : ℂ) :=
    MeasurableL2FieldAE.realization_ae ν Fc hFc ω
      ((MeasurableL2FieldAE.section_memLp_iff ν Fc hFc ω).mp (hSec ω))
  exact bessel μ (MeasurableL2FieldAE.realization ν Fc) hm F hF hRep hM hBound hC hCorr hΛ hρ

end SHEStochastic.AveragedHeatCorrelation
