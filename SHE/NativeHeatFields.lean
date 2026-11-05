module

public import SHE.NativeFirstWordMeanPower
public import SHE.VariableOldGaussian
public import SHE.PhysicalProfile

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Actual Borel native physical means and heat edges at varying time.
The unit-circle and 2pi-circle normalizations are identified exactly. -/
namespace SHE.NativeHeatFields
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore HeatHistoryScore HeatTorus HeatTorusKernel GaussianGramScore GaussianIncrement
  MeasurableGaussianScores NativeMeanFields NativeMeanScoreKernel MeasurableGeneralizedInverse
  GaussianWordFields NativeGaussianFirstWord GaussianAudit NativeOldRoot
  NativeFirstWordMeanTree NativeFirstWordMeanPower GaussianWordMeanDerivative
  ProfileVariance OldFractionHeatScale FirstWordPowers ProfileL2 PhysicalProfile
  RealHeatCovarianceMean StoppedMeanEnergy
open scoped InnerProductSpace NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨by positivity⟩
variable {X:Type*}[MeasurableSpace X]{n:ℕ}

theorem push_unitHeatKernel {t:ℝ}(ht:0<t)(a:UnitAddCircle):
    CircleNormalization.push (unitHeatKernel t a)=circleHeat (4*π^2*t) (CircleNormalization.scale 1 (2*π) a):=by
  apply (fourierBasis (T:=2*π)).repr.injective
  apply lp.ext
  funext k
  simp only[fourierBasis_repr,CircleNormalization.fourierCoeff_push]
  rw[fourierCoeff_unitHeatKernel ht,circleHeat_fourierCoeff (by positivity)]
  simp only[heatCoeff,CircleNormalization.fourier_scale]

def physicalDirection (target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(Λ:ℝ)(d:HeatTorus.CircleL2):State n:=
  WithLp.toLp 2 (fun i=>exp (-Λ*target i)*physicalHeatMean (CircleNormalization.push d)
    (target i,nativeCenter a i))

theorem physicalDirection_measurable (target:X→Fin n→ℝ)(ht:∀i,Measurable (fun x=>target x i))
    (a:X→Fin n→UnitAddCircle)(ha:∀i,Measurable (fun x=>a x i))(Λ:ℝ)(d:HeatTorus.CircleL2):
    Measurable (fun x=>physicalDirection (target x) (a x) Λ d):=by
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  exact (((ht i).const_mul (-Λ)).exp).mul
    ((physicalHeatMean_measurable (CircleNormalization.push d)).comp
      ((ht i).prodMk ((CircleNormalization.continuous_scale 1 (2*π)).measurable.comp (ha i))))

/-- The Borel physical heat-mean field is exactly the signed mean direction
used in the canonical full-history score energy. -/
theorem physicalDirection_eq (target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(Λ:ℝ)
    (t:Fin n→ℝ)(ht:∀i,0<t i)(hage:∀i,target i=4*π^2*t i)(act:∀i,0<target i)(d:HeatTorus.CircleL2):
    physicalDirection target a Λ d=meanDirection
      (dampedSynthesis target target a 0 Λ t (fun i=>by simpa using hage i) act) d:=by
  apply PiLp.ext
  intro i
  rw[meanDirection_apply,dampedSynthesis_basis]
  change exp (-Λ*target i)*physicalHeatMean (CircleNormalization.push d) (target i,nativeCenter a i)=
    (inner ℂ ((Real.exp (-Λ*(target i-0)):ℂ) • unitHeatKernel (t i) (a i)) d).re
  rw[physicalHeatMean_eq (act i),inner_smul_left]
  have hi:=CircleNormalization.push.inner_map_map (unitHeatKernel (t i) (a i)) d
  rw[push_unitHeatKernel (ht i)] at hi
  rw[←hage i] at hi
  rw[←hi]
  simp only[sub_zero,Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,nativeCenter]

def physicalEdge (r:ℝ)(y:UnitAddCircle):ℂ:=heatPhysical r 0 (CircleNormalization.scale 1 (2*π) y)

theorem physicalEdge_measurable:Measurable (fun p:ℝ×UnitAddCircle=>physicalEdge p.1 p.2):=
  heatPhysical_joint_measurable.comp
    ((measurable_fst.prodMk measurable_const).prodMk
      ((CircleNormalization.continuous_scale 1 (2*π)).measurable.comp measurable_snd))

/-- The jointly Borel physical old heat edge is the same actual kernel as
the positive normalized heat-tree kernel used in the spatial estimate. -/
theorem physicalEdge_ae_kernel {r:ℝ}(hr:0<r):
    ∀ᵐ y:UnitAddCircle ∂(haarAddCircle (T:=(1:ℝ))),
      physicalEdge r y=HeatMarkov.kernel (r/(4*π^2)) (div_pos hr (by positivity)) y:=by
  have he:4*π^2*(r/(4*π^2))=r:=by field_simp
  have h0:(CircleNormalization.scale 1 (2*π)) (0:UnitAddCircle)=(0:HeatCircle):=map_zero _
  have hp:=CircleNormalization.pull_ae 1 (2*π) (circleHeat r (0:HeatCircle))
  have hk:=HeatMarkov.unitHeatKernel_ae (t:=r/(4*π^2)) (by positivity) (0:UnitAddCircle)
  have hphys:∀ᵐy:UnitAddCircle ∂haarAddCircle,
      physicalEdge r y=circleHeat r 0 (CircleNormalization.scale 1 (2*π) y):=by
    have hh:=(CircleNormalization.scale_measurePreserving 1 (2*π)).quasiMeasurePreserving.ae (heatPhysical_ae hr 0)
    convert! hh using 1
  have hunit:unitHeatKernel (r/(4*π^2)) (0:UnitAddCircle)=
      CircleNormalization.pull 1 (2*π) (circleHeat r (0:HeatCircle)):=by
    unfold unitHeatKernel
    rw[he,h0]
  filter_upwards[hp,hk,hphys] with y hpy hky hy
  rw[sub_zero,hunit] at hky
  exact hy.trans (hpy.symm.trans hky)

end SHE.NativeHeatFields
