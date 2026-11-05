module

public import SHE.NativeParentOutputEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.NativeParentOutputEnergyAE
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
open scoped ENNReal BigOperators
local instance nativeParentOutputEnergyAE_period:Fact (0<2*π):=⟨by positivity⟩
local instance nativeParentOutputEnergyAE_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance nativeParentOutputEnergyAE_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

/-- Changing a kernel on a fixed null set of genuine spatial pairs
does not alter any of its realized native negative kernels. -/
theorem negativeKernel_congr_spatial
    {F G:Ω×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F) (hG:Measurable G)
    {B:ℝ} (hB:0≤B) (hbF:∀ω y x,‖F (ω,(y,x))‖≤B) (hbG:∀ω y x,‖G (ω,(y,x))‖≤B)
    (he:∀ω,∀ᵐz:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,F (ω,z)=G (ω,z))
    {Λ ρ:ℝ} (hΛ:1≤Λ) (hρ:0≤ρ) (ω:Ω):
    NativeRandomKernel.negativeKernel Λ ρ hΛ hρ F ω=
      NativeRandomKernel.negativeKernel Λ ρ hΛ hρ G ω := by
  have hc:∀ᵐy:HeatCircle∂haarAddCircle,
      NativeRandomKernel.column F (ω,y)=NativeRandomKernel.column G (ω,y):=by
    filter_upwards [Measure.ae_ae_of_ae_prod (he ω)] with y hy
    apply Lp.ext
    filter_upwards [NativeRandomKernel.column_ae hF hbF ω y,
      NativeRandomKernel.column_ae hG hbG ω y,hy] with x hFx hGx hx
    exact hFx.trans (hx.trans hGx.symm)
  apply Lp.ext
  filter_upwards [NativeRandomKernel.negativeKernel_ae hΛ hρ hF hB hbF ω,
    NativeRandomKernel.negativeKernel_ae hΛ hρ hG hB hbG ω,hc] with y hFy hGy hy
  exact hFy.trans ((congrArg (OneInputOperator.besselHalf Λ ρ hΛ hρ) hy).trans hGy.symm)

/-- The native finite-parent trace consumes a genuine JOINT spatial AE
envelope, as supplied by the translated physical row-range theorem.
There is no substitution into a fixed-frame exceptional set. -/
theorem energy (μ:Measure Ω) [IsProbabilityMeasure μ]
    {F:Ω×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀ω y x,‖F (ω,(y,x))‖≤B)
    (a:HeatCircle→ℝ) (ha:Measurable a) (ha0:∀x,0≤a x)
    (hai:Integrable (fun x=>a x^2) haarAddCircle) {E:ℝ}
    (he:(∫x,a x^2 ∂haarAddCircle)≤E)
    (n:ℕ) (hn:0<n) (age:Fin n→ℝ) (shift:Fin n→HeatCircle)
    (hage:∀i,0<age i) {w:ℝ} (hw:0<w) (hw1:w≤1) (hmax:∀i,age i≤w)
    {Λ ρ:ℝ} (hΛ:1≤Λ) (hρ:0<ρ) (hρhalf:ρ<1/2)
    (hsharp:∀ᵐz:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      ProfileL2.normTwo μ (fun ω=>‖F (ω,z)‖)≤
        a z.2*∑i,(age i)^(1/4:ℝ)*
          ‖NativeHeatSpan.kernel (8*age i) (by have := hage i; positivity) z.1 (z.2+shift i)‖):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ)≤
        (n:ℝ)^2*(4*π^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
          (NativeHeatSpan.clock w)^ρ*E := by
  let H:HeatCircle×HeatCircle→ℝ:=fun z=>a z.2*∑i,(age i)^(1/4:ℝ)*
    ‖NativeHeatSpan.kernel (8*age i) (by have := hage i; positivity) z.1 (z.2+shift i)‖
  have hH:Measurable H:=by
    apply (ha.comp measurable_snd).mul
    apply Finset.measurable_sum
    intro i _
    apply measurable_const.mul
    simp_rw [NativeHeatSpan.kernel_eq_physical]
    exact ((NativeHeatSpan.continuous_heatPhysical_space (by have := hage i;positivity:0<8*age i)).comp
      (continuous_fst.prodMk (continuous_snd.add continuous_const))).norm.measurable
  have hH0(z:HeatCircle×HeatCircle):0≤H z:=mul_nonneg (ha0 z.2)
    (Finset.sum_nonneg (fun i _=>mul_nonneg (rpow_nonneg (hage i).le _) (norm_nonneg _)))
  let good:Set (HeatCircle×HeatCircle):={z|ProfileL2.normTwo μ (fun ω=>‖F (ω,z)‖)≤H z}
  have hNm:Measurable (fun z:HeatCircle×HeatCircle=>ProfileL2.normTwo μ (fun ω=>‖F (ω,z)‖)):=by
    apply Real.continuous_sqrt.measurable.comp
    exact (((hF.comp (measurable_snd.prodMk measurable_fst)).norm).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hgood:MeasurableSet good:=measurableSet_le hNm hH
  let G:Ω×(HeatCircle×HeatCircle)→ℂ:=fun z=>if z.2∈good then F z else 0
  have hG:Measurable G:=Measurable.ite (hgood.preimage measurable_snd) hF measurable_const
  have hGb(ω:Ω)(y x:HeatCircle):‖G (ω,(y,x))‖≤B:=by
    dsimp only [G]
    split_ifs
    · exact hb ω y x
    · simpa only [norm_zero] using hB
  have hGs(y x:HeatCircle):ProfileL2.normTwo μ (fun ω=>‖G (ω,(y,x))‖)≤H (y,x):=by
    by_cases hg:(y,x)∈good
    · have heq:(fun ω=>‖G (ω,(y,x))‖)=(fun ω=>‖F (ω,(y,x))‖):=by
        funext ω
        simp only [G,if_pos hg]
      rw [heq]
      exact hg
    · have heq:(fun ω=>‖G (ω,(y,x))‖)=(fun _=>0):=by
        funext ω
        simp only [G,if_neg hg,norm_zero]
      rw [heq]
      simpa only [ProfileL2.normTwo,zero_pow (by decide : 2≠0),integral_zero,Real.sqrt_zero] using hH0 (y,x)
  have hsame(ω:Ω):NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω=
      NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le G ω:=by
    apply negativeKernel_congr_spatial hF hG hB hb hGb _ hΛ hρ.le ω
    intro ω'
    filter_upwards [hsharp] with z hz
    exact (if_pos hz).symm
  have hh:=NativeParentOutputEnergy.energy μ hG hB hGb a ha ha0 hai he n hn age shift hage
    hw hw1 hmax hΛ hρ hρhalf hGs
  simpa only [←hsame] using hh

end SHE.NativeParentOutputEnergyAE
