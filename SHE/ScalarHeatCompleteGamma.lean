module

public import SHE.ScalarHeatSignedTrace
public import SHE.ScalarHeatBandHaarTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace SHE.ScalarHeatCompleteGamma
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier NativeHeatObservation ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal
local instance scalarHeatCompleteGamma_period : Fact (0<2*π):=⟨by positivity⟩
local instance scalarHeatCompleteGamma_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance scalarHeatCompleteGamma_sigma : MeasurableSpace CircleL2:=borel _
local instance scalarHeatCompleteGamma_borel : BorelSpace CircleL2:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

theorem norm_add_sq_le {E : Type*} [NormedAddCommGroup E] (u v : E) :
    ‖u+v‖^2≤2*‖u‖^2+2*‖v‖^2 := by
  have hn:=norm_add_le u v
  have hs:=sq_nonneg (‖u‖-‖v‖)
  nlinarith [norm_nonneg (u+v),norm_nonneg u,norm_nonneg v]

theorem trace_add {I E : Type*} [NormedAddCommGroup E] (f g : I→E)
    (hf : Summable (fun i=>‖f i‖^2)) (hg : Summable (fun i=>‖g i‖^2)) :
    Summable (fun i=>‖f i+g i‖^2) ∧
      (∑' i,‖f i+g i‖^2)≤2*(∑' i,‖f i‖^2)+2*(∑' i,‖g i‖^2) := by
  have hs : Summable (fun i=>2*‖f i‖^2+2*‖g i‖^2):=(hf.mul_left 2).add (hg.mul_left 2)
  have hh : Summable (fun i=>‖f i+g i‖^2):=
    Summable.of_nonneg_of_le (fun i=>sq_nonneg _) (fun i=>norm_add_sq_le _ _) hs
  refine ⟨hh,?_⟩
  have hl:=hh.tsum_le_tsum (fun i=>norm_add_sq_le (f i) (g i)) hs
  simpa only [(hf.mul_left 2).tsum_add (hg.mul_left 2),tsum_mul_left] using hl

/-- The physical displaced-gradient operator is exactly the difference
of the two actual Gaussian-gradient multipliers. Both fields may be
arbitrarily correlated with the coefficient and the future variance. -/
theorem multiplier_difference {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x y : P×HeatCircle→ℝ} (hσm : Measurable σ) (hxm : Measurable x) (hym : Measurable y) (p : P)
    (hσ : ∀ᵐ z∂haarAddCircle,lo≤σ (p,z)) (v : CircleL2) :
    let B:=(H*ScalarHeatBandEnvelope.constant β 0)*CompactMollifier.radius (j+1)^(β-1)*decay (CompactMollifier.radius (j+1)) lo ((3-β)/2)
    let AX:=NativeMultiplierTrace.multiplier (ScalarHeatSingleMultiplier.multiplier a j σ x p) B
      (ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσm hxm p hσ)
    let AY:=NativeMultiplierTrace.multiplier (ScalarHeatSingleMultiplier.multiplier a j σ y p) B
      (ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσm hym p hσ)
    let AD:=NativeMultiplierTrace.multiplier (ScalarHeatBandMultipliers.multiplier a j σ x y p)
      (ScalarHeatBandMultipliers.cap H β j) (ScalarHeatBandMultipliers.multiplier_bound ha hH hβ hβ1 hh j hσm hxm hym p)
    AY v-AX v=AD v := by
  intro B AX AY AD
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (AY v) (AX v),
    NativeMultiplierTrace.multiplier_ae _ _ _ v,NativeMultiplierTrace.multiplier_ae _ _ _ v,
    NativeMultiplierTrace.multiplier_ae _ _ _ v,
    ScalarHeatSingleMultiplier.multiplier_ae ha hH hβ hβ1 hh j hσm hxm p,
    ScalarHeatSingleMultiplier.multiplier_ae ha hH hβ hβ1 hh j hσm hym p,
    ScalarHeatBandMultipliers.multiplier_ae ha hH hβ hβ1 hh j hσm hxm hym p]
    with z hsub hx hy hd hxf hyf hdf
  rw [hsub]
  change AY v z-AX v z=AD v z
  change AY v z=ScalarHeatSingleMultiplier.multiplier a j σ y p z*v z at hy
  change AX v z=ScalarHeatSingleMultiplier.multiplier a j σ x p z*v z at hx
  change AD v z=ScalarHeatBandMultipliers.multiplier a j σ x y p z*v z at hd
  rw [hy,hx,hd,hxf,hyf,hdf]
  simp only [ScalarHeatSingleMultiplier.field,ScalarHeatBandMultipliers.field,Complex.ofReal_sub]
  ring

/-- A SINGLE bound for the literal complete martingale difference:
current Gaussian gradient times the current Haar field MINUS frozen
Gaussian gradient times the frozen Haar field. Its two distinct terms
retain respectively the actual negative input energy and the clipped
current/frozen displacement energy. No independence is used. -/
theorem exists_complete_trace (m U : ℝ) (hm : 0<m) {ρ : ℝ} (hρ : 0<ρ) (hρhalf : ρ<1/2) :
    ∃ C : ℝ,0<C ∧ ∀ (a : ℝ→ℝ) (ha : BoundedSmooth a) (H β lo : ℝ)
      (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
      (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
      (σ x y : P×HeatCircle→ℝ) (hσm : Measurable σ) (hxm : Measurable x) (hym : Measurable y) (p : P)
      (hσ : ∀ᵐ z∂haarAddCircle,lo≤σ (p,z))
      (hi : Integrable (fun z=>(y (p,z)-x (p,z))^2) haarAddCircle)
      (Λ t : ℝ) (hΛ : 1≤Λ) (ht : 0<t) (ht1 : t≤1) (c d : FiniteHaar.EllipticField m U),
    let r:=CompactMollifier.radius (j+1)
    let B:=(H*ScalarHeatBandEnvelope.constant β 0)*r^(β-1)*decay r lo ((3-β)/2)
    let AX:=NativeMultiplierTrace.multiplier (ScalarHeatSingleMultiplier.multiplier a j σ x p) B
      (ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσm hxm p hσ)
    let AY:=NativeMultiplierTrace.multiplier (ScalarHeatSingleMultiplier.multiplier a j σ y p) B
      (ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσm hym p hσ)
    let col:=fun q : FiniteHaar.HaarNode=>OneInputOperator.besselHalf Λ ρ hΛ hρ.le
      (AY (circleHeatOperator t ht.le (CircleNormalization.push (FiniteHaar.globalHaarColumn q d.1)))-
       AX (circleHeatOperator t ht.le (CircleNormalization.push (FiniteHaar.globalHaarColumn q c.1))))
    Summable (fun q=>‖col q‖^2) ∧
      (∑' q,‖col q‖^2)≤
        2*C*B^2*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*NativeSignedHaarProcess.inputEnergy hΛ hρ.le c d+
        2*U*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2))*
          ((2*H*ScalarHeatGradientDifference.constant β)*r^(β-1)*decay r lo ((3-β)/2))^2*
          min 1 ((∫ z,(y (p,z)-x (p,z))^2 ∂haarAddCircle)/r^2) := by
  obtain ⟨C,hC,htrace⟩:=ScalarHeatSignedTrace.exists_gradient_signed_trace (P:=P) m U hm hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro a ha H β lo hH hβ hβ1 hlo hh j σ x y hσm hxm hym p hσ hi Λ t hΛ ht ht1 c d r B AX AY col
  let AD:=NativeMultiplierTrace.multiplier (ScalarHeatBandMultipliers.multiplier a j σ x y p)
    (ScalarHeatBandMultipliers.cap H β j) (ScalarHeatBandMultipliers.multiplier_bound ha hH hβ hβ1 hh j hσm hxm hym p)
  let f:=fun q : FiniteHaar.HaarNode=>OneInputOperator.besselHalf Λ ρ hΛ hρ.le
    (AY (circleHeatOperator t ht.le (CircleNormalization.push (FiniteHaar.globalHaarColumn q d.1-FiniteHaar.globalHaarColumn q c.1))))
  let g:=fun q : FiniteHaar.HaarNode=>OneInputOperator.besselHalf Λ ρ hΛ hρ.le
    (AD (circleHeatOperator t ht.le (CircleNormalization.push (FiniteHaar.globalHaarColumn q c.1))))
  have hf:=htrace a ha H β lo hH hβ hβ1 hlo hh j σ y hσm hym p hσ Λ t hΛ ht ht1 c d
  have hg:=ScalarHeatBandHaarTrace.displaced_gradient_trace ha hH hβ hβ1 hlo hh j hσm hxm hym p hσ hi hΛ hρ.le hρhalf ht ht1 hm c
  have he (q : FiniteHaar.HaarNode) : col q=f q+g q := by
    have hm:=multiplier_difference ha hH hβ hβ1 hlo hh j hσm hxm hym p hσ
      (circleHeatOperator t ht.le (CircleNormalization.push (FiniteHaar.globalHaarColumn q c.1)))
    change AY _-AX _=AD _ at hm
    dsimp only [col,f,g]
    rw [map_sub,map_sub,map_sub,map_sub]
    rw [←hm]
    simp only [map_sub]
    abel
  have hs:=trace_add f g hf.1 hg.1
  refine ⟨by simpa only [←he] using hs.1,?_⟩
  have hle:=hs.2.trans (add_le_add (mul_le_mul_of_nonneg_left hf.2 (by norm_num))
    (mul_le_mul_of_nonneg_left hg.2 (by norm_num)))
  simpa only [←he,B,r,mul_assoc] using hle

end SHE.ScalarHeatCompleteGamma
