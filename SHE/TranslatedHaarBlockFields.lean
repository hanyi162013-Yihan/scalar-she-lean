module

public import SHE.NativeHaarBlockDirections

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.TranslatedHaarBlockFields
open Set MeasureTheory Real AddCircle FiniteHaar CircleHeat StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores BlockDefectScores
local instance translatedHaarBlockFields_period:Fact (0<2*π):=⟨by positivity⟩
local instance translatedHaarBlockFields_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

theorem synthesis_basis {n g:ℕ}(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)
    (t:Fin n→ℝ)(ht:∀i,0<t i)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀j i,u<groupData label rep σ j i)(j:Fin g)(quadratic:Bool)(i:Fin n):
    StronglyMeasurable (fun x:UnitAddCircle=>
      (if quadratic then StoppedDefectBlockProjection.synthesis label rep σ target
        (fun l=>a l+x) u Λ t hage act j else StoppedCurrentBlockHaarTrace.synthesis label rep σ target
          (fun l=>a l+x) u t hage act j) (EuclideanSpace.basisFun (Fin n) ℝ i)):=by
  have hm:=(HeatChristoffelTransfer.continuous_translate_action.comp (continuous_id.prodMk
    (continuous_const:Continuous (fun _:UnitAddCircle=>unitHeatKernel (t i) (a i))))).stronglyMeasurable
  by_cases hij:label i=j
  · cases quadratic with
    | false=>
      convert! hm using 1
      funext x
      simp only [Bool.false_eq_true,if_false,StoppedCurrentBlockHaarTrace.basis,if_pos hij]
      change unitHeatKernel (t i) (a i+x)=translate x (unitHeatKernel (t i) (a i))
      rw [translate_unitHeatKernel (ht i)]
    | true=>
      have hs:=hm.const_smul (1-(exp (-Λ*(σ i-u)):ℂ))
      convert! hs using 1
      funext x
      simp only [if_true,StoppedDefectBlockProjection.synthesis,LinearMap.comp_apply,
        LinearMap.restrictScalars_apply,Submodule.subtype_apply,defectBlockRow_basis,if_pos hij]
      change (1-(exp (-Λ*(σ i-u)):ℂ)) • unitHeatKernel (t i) (a i+x)=
        (1-(exp (-Λ*(σ i-u)):ℂ)) • translate x (unitHeatKernel (t i) (a i))
      rw [translate_unitHeatKernel (ht i)]
  · convert! (stronglyMeasurable_const:StronglyMeasurable (fun _:UnitAddCircle=>(0:HeatTorus.CircleL2))) using 1
    funext x
    cases quadratic <;>
      simp only [Bool.false_eq_true,if_false,if_true,StoppedCurrentBlockHaarTrace.basis,if_neg hij,
        StoppedDefectBlockProjection.synthesis,LinearMap.comp_apply,LinearMap.restrictScalars_apply,
        Submodule.subtype_apply,defectBlockRow_basis]

theorem direction {n g:ℕ}(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)
    (t:Fin n→ℝ)(ht:∀i,0<t i)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀j i,u<groupData label rep σ j i)(j:Fin g)(quadratic:Bool)(d:HeatTorus.CircleL2):
    Measurable (fun x:UnitAddCircle=>meanDirection
      (if quadratic then StoppedDefectBlockProjection.synthesis label rep σ target
        (fun l=>a l+x) u Λ t hage act j else StoppedCurrentBlockHaarTrace.synthesis label rep σ target
          (fun l=>a l+x) u t hage act j) d):=
  meanDirection_measurable _ (synthesis_basis label rep σ target a u Λ t ht hage act j quadratic) d

/-- Literal common-Haar contraction of a varying actual Hessian is a
Borel scalar field before any root or old-history averaging. -/
theorem packet {X:Type*}[MeasurableSpace X]{n:ℕ}
    (B:X→State n→L[ℝ]State n→L[ℝ]ℝ)(hB:Measurable B)
    (E V:HaarNode→X→State n)(hE:∀j,Measurable (E j))(hV:∀j,Measurable (V j)):
    Measurable (fun x:X=>∑'j:HaarNode,B x (V j x) (E j x)):=by
  apply Measurable.tsum
  intro j
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp
    (((continuous_fst.clm_apply continuous_snd).measurable.comp (hB.prodMk (hV j))).prodMk (hE j))

end SHE.TranslatedHaarBlockFields
