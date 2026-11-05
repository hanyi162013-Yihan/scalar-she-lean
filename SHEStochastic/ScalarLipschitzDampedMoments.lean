module

public import SHEStochastic.ScalarLipschitzDampedEnergy
public import SHEStochastic.ScalarLipschitzTimeMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzDampedMoments
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzDampedEnergy ScalarLipschitzKernelBounds ScalarLipschitzConvolution
  ScalarLipschitzRawBounds ScalarLipschitzItoMoment
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def weightedMoment (γ : ℝ) (Z : ℝ≥0 → Ω → RealL2) (t : ℝ≥0) : ℝ≥0∞ :=
  (timeWeight γ t)^8*moment 16 (Z t) μ

omit [IsProbabilityMeasure μ] in
theorem weightedMoment_unweight (γ : ℝ) (Z : ℝ≥0 → Ω → RealL2) (t : ℝ≥0) :
    moment 16 (Z t) μ=(timeWeight (-γ) t)^8*weightedMoment (μ := μ) γ Z t := by
  unfold weightedMoment
  rw [←mul_assoc,←mul_pow,mul_comm (timeWeight (-γ) t),timeWeight_inverse,one_pow,one_mul]

omit [IsProbabilityMeasure μ] in
theorem weightedMoment_add (γ : ℝ) (U V : ℝ≥0 → Ω → RealL2) (t : ℝ≥0)
    (hU : Measurable (U t)) (hV : Measurable (V t)) :
    weightedMoment (μ := μ) γ (fun s ω => U s ω+V s ω) t≤
      ENNReal.ofReal ((2 : ℝ)^16)*(weightedMoment (μ := μ) γ U t+weightedMoment (μ := μ) γ V t) := by
  have h₁ : Measurable (fun ω => ENNReal.ofReal (‖U t ω‖^16)) := (hU.norm.pow_const _).ennreal_ofReal
  have h₂ : Measurable (fun ω => ENNReal.ofReal (‖V t ω‖^16)) := (hV.norm.pow_const _).ennreal_ofReal
  have h : moment 16 (fun ω => U t ω+V t ω) μ≤
      ENNReal.ofReal ((2 : ℝ)^16)*(moment 16 (U t) μ+moment 16 (V t) μ) := by
    calc
      _ ≤ ∫⁻ ω,ENNReal.ofReal ((2 : ℝ)^16)*
          (ENNReal.ofReal (‖U t ω‖^16)+ENNReal.ofReal (‖V t ω‖^16)) ∂μ := by
        apply lintegral_mono
        intro ω
        change ENNReal.ofReal (‖U t ω+V t ω‖^16)≤ENNReal.ofReal ((2 : ℝ)^16)*
          (ENNReal.ofReal (‖U t ω‖^16)+ENNReal.ofReal (‖V t ω‖^16))
        rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _).trans
          (pow_add_bound _ _ (norm_nonneg _) (norm_nonneg _) _)
      _ = _ := by
        unfold moment
        have hsum : Measurable (fun ω => ENNReal.ofReal (‖U t ω‖^16)+ENNReal.ofReal (‖V t ω‖^16)) :=
          h₁.add h₂
        rw [lintegral_const_mul'' (ENNReal.ofReal ((2 : ℝ)^16)) hsum.aemeasurable,
          lintegral_add_left h₁]
  unfold weightedMoment
  apply (mul_le_mul_right h _).trans_eq
  ring

variable {I : Type*} [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))

def growthConstant (g : ℝ → ℝ) (C H γ : ℝ) : ℝ :=
  (NativeScalarBDG.constant 3 : ℝ)*(heatConstant H*BieleckiKernel.mass γ)^8*
    ((4*(‖g 0‖+C)^2)^8*2^8)

theorem growthConstant_nonneg (g : ℝ → ℝ) (C H γ : ℝ) : 0≤growthConstant g C H γ := by
  unfold growthConstant
  positivity

theorem growthConstant_tendsto (g : ℝ → ℝ) (C H : ℝ) :
    Tendsto (growthConstant g C H) atTop (𝓝 0) := by
  unfold growthConstant
  have h := (((BieleckiKernel.mass_tends_zero.const_mul (heatConstant H)).pow 8).const_mul
    (NativeScalarBDG.constant 3 : ℝ)).mul_const ((4*(‖g 0‖+C)^2)^8*2^8)
  simpa only [mul_zero,zero_pow (by decide : 8≠0),zero_mul] using h

/-- The sixteenth moment of the true convolution has a small
Bielecki factor. No pointwise path cap or uniform bound on g is used. -/
theorem convolution_bound {γ : ℝ} (hγ : 0<γ) (D : ℝ) (hD : 0≤D)
    (hM : ∀ᵐ s ∂PredictableL2.timeMeasure H,weightedMoment (μ := μ) γ U s≤ENNReal.ofReal D)
    (t : ℝ≥0) (ht : t≤H)
    (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H)) :
    (timeWeight γ t)^8*moment 16 ((ito e P).integral (input e hg U hU t hE)) μ≤
      ENNReal.ofReal (growthConstant g (C : ℝ) (H : ℝ) γ*(1+D)) := by
  let a := input e hg U hU t hE
  let k := fun s : ℝ≥0 => ENNReal.ofReal (heatConstant (H : ℝ))*
    BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))
  let f := fun p : ℝ≥0×Ω => timeWeight γ p.1*coeffSquare hg U p
  let c := Real.exp (-γ*(t : ℝ))
  let G := (growth g C)^8*2^8
  have hG : 0≤G := by dsimp only [G]; positivity
  have hc : c≥0 := (Real.exp_pos _).le
  have hc2 : ENNReal.ofReal (c^2)=timeWeight γ t := by
    unfold c timeWeight
    rw [pow_two,←Real.exp_add]
    congr 2
    ring
  have hk : Measurable k := measurable_const.mul ((BieleckiKernel.measurable H γ).comp
    (measurable_const.sub NNReal.continuous_coe.measurable))
  have hf : Measurable f := ((timeWeight_measurable γ).comp measurable_fst).mul
    (coeffSquare_measurable hg U hU)
  have hsec (s : ℝ≥0) : Measurable (fun ω => (coeffSquare hg U (s,ω))^8) := by
    exact ((coeffSquare_measurable hg U hU).comp (measurable_const.prodMk measurable_id)).pow_const _
  have hUs (s : ℝ≥0) : Measurable (U s) :=
    (hU.mono (predictable_le_product F)).measurable.comp (measurable_const.prodMk measurable_id)
  have hF : ∀ᵐ s ∂PredictableL2.timeMeasure H,(∫⁻ ω,(f (s,ω))^8 ∂μ)≤
      ENNReal.ofReal G*(1+ENNReal.ofReal D) := by
    filter_upwards [hM] with s hs
    dsimp only [f]
    simp_rw [mul_pow]
    rw [lintegral_const_mul'' ((timeWeight γ s)^8) (hsec s).aemeasurable]
    have h := mul_le_mul_right (coeffSquare_eighth (μ := μ) hg U s (hUs s)) ((timeWeight γ s)^8)
    refine h.trans ?_
    rw [←mul_assoc,mul_comm ((timeWeight γ s)^8),mul_assoc,mul_add, mul_one]
    exact mul_le_mul_right (add_le_add (pow_le_one₀ bot_le (timeWeight_le_one hγ.le s)) hs) _
  have ha : ∀ᵐ p ∂energyMeasure μ H,ENNReal.ofReal (‖(c • a) p‖^2)≤k p.1*f p := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_smul c a),input_ae e hg U hU t hE] with p hc' ha
    rw [hc',Pi.smul_apply,ha,norm_smul,mul_pow,Real.norm_eq_abs,abs_of_nonneg hc,
      ENNReal.ofReal_mul (sq_nonneg c),hc2]
    exact raw_growth e hg ht γ U p
  have hb := moment_of_density (ito e P) _ (by intro u; exact bdg e P u)
    (c • a) k hk f hf _ hF ha
  have hmoment : moment 16 ((ito e P).integral (c • a)) μ =
      (timeWeight γ t)^8*moment 16 ((ito e P).integral a) μ := by
    rw [map_smul]
    unfold moment
    have hsec' : Measurable (fun ω => ENNReal.ofReal (‖(ito e P).integral a ω‖^16)) :=
      ((Lp.stronglyMeasurable ((ito e P).integral a)).norm.pow 16).measurable.ennreal_ofReal
    rw [←lintegral_const_mul'' ((timeWeight γ t)^8) hsec'.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_smul c ((ito e P).integral a)] with ω hω
    rw [hω,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,mul_pow,
      ENNReal.ofReal_mul (pow_nonneg hc _),show (16 : ℕ)=2*8 by decide,pow_mul,
      ENNReal.ofReal_pow (sq_nonneg c),hc2]
  rw [hmoment] at hb
  refine hb.trans ?_
  have hkm : (∫⁻ s,k s ∂PredictableL2.timeMeasure H)≤
      ENNReal.ofReal (heatConstant (H : ℝ)*BieleckiKernel.mass γ) := by
    dsimp only [k]
    have hkm' : Measurable (fun s : ℝ≥0 => BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))) :=
      (BieleckiKernel.measurable H γ).comp (measurable_const.sub NNReal.continuous_coe.measurable)
    have hk0 : 0≤heatConstant (H : ℝ) := heatConstant_nonneg H.property
    rw [lintegral_const_mul'' (ENNReal.ofReal (heatConstant (H : ℝ))) hkm'.aemeasurable,
      ENNReal.ofReal_mul (q := BieleckiKernel.mass γ) hk0]
    exact mul_le_mul_right (ScalarLipschitzWeightedMoment.damped_mass H hγ ht) _
  refine (mul_le_mul_left (mul_le_mul_right (pow_le_pow_left' hkm 8) _) _).trans_eq ?_
  let L := heatConstant (H : ℝ)*BieleckiKernel.mass γ
  have hL : 0≤L := mul_nonneg (heatConstant_nonneg H.property) (BieleckiKernel.mass_nonneg hγ.le)
  let B := NativeScalarBDG.constant 3
  change (B : ℝ≥0∞)*ENNReal.ofReal L^8*(ENNReal.ofReal G*(1+ENNReal.ofReal D))=
    ENNReal.ofReal ((B : ℝ)*L^8*G*(1+D))
  rw [←ENNReal.ofReal_pow (n := 8) hL,←ENNReal.ofReal_one,←ENNReal.ofReal_add zero_le_one hD,
    ←ENNReal.ofReal_coe_nnreal (p := B)]
  rw [←ENNReal.ofReal_mul (q := 1+D) hG,←ENNReal.ofReal_mul (q := L^8) (show 0≤(B : ℝ) from B.property),
    ←ENNReal.ofReal_mul (q := G*(1+D)) (show 0≤(B : ℝ)*L^8 from mul_nonneg B.property (pow_nonneg hL _))]

  congr 1
  ring

end SHEStochastic.ScalarLipschitzDampedMoments
