module

public import SHE.ScalarHeatPairedMultipliers

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2900000
namespace SHE.ScalarHeatPairedGamma
open Set MeasureTheory AddCircle Real StoppedFourier FiniteHaar ScalarGaussianSemigroup SmoothCylinders ScalarHeatBandEnvelope
open scoped ENNReal NNReal
local instance scalarHeatPairedGamma_period : Fact (0<2*π):=⟨by positivity⟩
variable {P : Type*} [MeasurableSpace P]

/-- A SINGLE complete paired scalar-band Gamma bound. Both actual and
frozen martingale terms, both root displacements, both variance slots
and both changed noise factors remain in the literal native operator.
All scalar multiplier norms are discharged by true energy estimates. -/
theorem exists_paired_trace (m U : ℝ) (hm : 0<m) {ρ : ℝ} (hρ : 0<ρ) (hρhalf : ρ<1/2) :
    ∃ C : ℝ,0<C ∧ ∀ (a : ℝ→ℝ) (ha : BoundedSmooth a) (H β lo : ℝ)
      (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
      (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
      (σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ)
      (hσ0 : Measurable σ0) (hσ1 : Measurable σ1) (hz0 : Measurable z0) (hz1 : Measurable z1)
      (hm0 : Measurable m0) (hm1 : Measurable m1) (p : P)
      (h0 : ∀ᵐ x∂haarAddCircle,lo≤σ0 (p,x)) (h1 : ∀ᵐ x∂haarAddCircle,lo≤σ1 (p,x))
      (hiZ : Integrable (fun x=>(z1 (p,x)-z0 (p,x))^2) haarAddCircle)
      (hiM : Integrable (fun x=>(m1 (p,x)-m0 (p,x))^2) haarAddCircle)
      (hiσ : Integrable (fun x=>(σ1 (p,x)-σ0 (p,x))^2) haarAddCircle)
      (Λ t : ℝ) (hΛ : 1≤Λ) (ht : 0<t) (ht1 : t≤1) (κ : ℝ) (hκ : 0<κ)
      (c0 c1 r0 r1 : EllipticField m U),
    let b:=ScalarHeatPairedMultipliers.six a j σ0 σ1 z0 z1 m0 m1 p
    let r:=CompactMollifier.radius (j+1)
    let B:=H*constant β 0*r^(β-1)*decay r lo ((3-β)/2)
    let CZ:=2*H*ScalarHeatGradientDifference.constant β*r^(β-1)*decay r lo ((3-β)/2)
    let CV:=(1/2:ℝ)*H*constant β 2*r^(β-3)*decay r lo ((5-β)/2)
    let hb:=ScalarHeatPairedMultipliers.bound ha hH hβ hβ1 hlo hh j hσ0 hσ1 hz0 hz1 hm0 hm1 p h0 h1
    let col:=fun (i : Fin 6) (f : CircleHeat.CircleL2) (q : HaarNode)=>
      OneInputOperator.besselHalf Λ ρ hΛ hρ.le
        (NativeMultiplierTrace.multiplier (b i) B (hb i) (circleHeatOperator t ht.le
          (CircleNormalization.push (globalHaarColumn q f))))
    let additive:=fun q=>col 0 (AdditiveHaarForcing.constantField κ hκ).1 q-
      col 3 (AdditiveHaarForcing.constantField κ hκ).1 q-
      col 2 (AdditiveHaarForcing.constantField κ hκ).1 q+col 5 (AdditiveHaarForcing.constantField κ hκ).1 q
    let residual:=fun q=>col 0 c0.1 q-col 3 r0.1 q-col 2 c1.1 q+col 5 r1.1 q
    Summable (fun q=>‖additive q‖^2+‖residual q‖^2) ∧
      (∑' q,(‖additive q‖^2+‖residual q‖^2))≤6*(
        C*B^2*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*NativeSignedHaarProcess.inputEnergy hΛ hρ.le c1 c0+
        HaarWeightedHeat.higherConstant m U hm 0 ρ*B^2*(NativeHeatSpan.clock t)^(ρ-1/2)*‖r0.1-r1.1‖^2+
        (κ+U)*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2))*(
          CZ^2*(min 1 ((∫ x,(z1 (p,x)-z0 (p,x))^2 ∂haarAddCircle)/r^2)+
            min 1 ((∫ x,(m1 (p,x)-m0 (p,x))^2 ∂haarAddCircle)/r^2))+
          2*CV^2*(∫ x,(σ1 (p,x)-σ0 (p,x))^2 ∂haarAddCircle))) := by
  obtain ⟨C,hC,htrace⟩:=NativePairedGammaTrace.exists_paired_trace m U hm hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro a ha H β lo hH hβ hβ1 hlo hh j σ0 σ1 z0 z1 m0 m1 hσ0 hσ1 hz0 hz1 hm0 hm1 p h0 h1 hiZ hiM hiσ
    Λ t hΛ ht ht1 κ hκ c0 c1 r0 r1 b r B CZ CV hb col additive residual
  have hB : 0≤B:=mul_nonneg
    (mul_nonneg (mul_nonneg hH (constant_nonneg β 0)) (rpow_nonneg (CompactMollifier.radius_pos _).le _))
    (le_min zero_le_one (rpow_nonneg (div_nonneg hlo.le (sq_nonneg _)) _))
  have htall:=htrace Λ t hΛ ht ht1 κ hκ b B hB hb c0 c1 r0 r1
  have hroots:=ScalarHeatPairedMultipliers.root_energy (σ1:=σ1) ha hH hβ hβ1 hlo hh j hσ0 hz0 hz1 hm0 hm1 p h0 hiZ hiM
  have hvar:=ScalarHeatPairedMultipliers.variance_energy (z0:=z0) (m0:=m0) ha hH hβ hβ1 hlo hh j hσ0 hσ1 hz1 hm1 p h0 h1 hiσ
  change ‖b 0-b 1‖^2+‖b 3-b 4‖^2≤CZ^2*_ at hroots
  change ‖b 1-b 2‖^2+‖b 4-b 5‖^2≤2*CV^2*_ at hvar
  have hU : 0≤U:=elliptic_upper_nonneg c0.1 m U hm c0.2.2
  have hcoef : 0≤(κ+U)*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2)):=
    mul_nonneg (add_nonneg hκ.le hU)
      (mul_nonneg (by linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf]) (rpow_nonneg ht.le _))
  refine ⟨htall.1,htall.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤6)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hcoef
  have hs:=add_le_add hroots hvar
  convert hs using 1 <;> ring

end SHE.ScalarHeatPairedGamma
