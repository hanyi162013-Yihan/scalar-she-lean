module

public import SHE.StoppedDefectBlockHaarTrace
public import SHE.StoppedDefectBlockBoundedTrace
public import SHE.FiniteHaarScoreTrace
public import SHE.TranslatedHaarBlockFields
public import SHE.HaarScoreTraceFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace SHE.StoppedFullSignedHaarTrace
open Set MeasureTheory Real AddCircle FiniteHaar CircleHeat StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores
open scoped BigOperators
local instance stoppedFullSignedHaarTrace_period:Fact (0<2*π):=⟨by positivity⟩
local instance stoppedFullSignedHaarTrace_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- The FULL original clipped Haar score has a true signed-input root
trace. Age blocks remain only a finite deterministic bound; no reduced
covariance or measurable partition choice is introduced. -/
theorem integral (n:ℕ):
    ∃h K θ:ℝ,0<h ∧ h≤1 ∧ 0<K ∧ 0<θ ∧
      ∀{g:ℕ}(hg:0<g)(label:Fin n→Fin g)(rep:Fin g→Fin n)(hrep:∀j,label (rep j)=j)
      (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ),0<Λ→
      ∀(t:Fin n→ℝ)(ht:∀i,0<t i),(∀i,t i≤h)→
      ∀(hage:∀i,target i-u=4*π^2*t i)(hages:∀i,σ i≤target i)
      (lower upper M:Fin g→ℝ)(A:ℝ),4*(g:ℝ)^2+1≤A→
      ∀(hlo:∀j,0<lower j),(∀j,lower j≤upper j)→(∀j,1≤M j)→(∀j,upper j≤M j*lower j)→
      ∀(hstlo:∀i,u+lower (label i)≤σ i)(hsthi:∀i,σ i≤u+upper (label i)),
      (∀j k,j<k→A*upper j≤lower k)→
      ∀(w N:Fin g→ℝ),(∀j,0<w j)→(∀j,1≤N j)→
      (∀j l,w j≤groupData label rep t j l)→
      (∀j l,groupData label rep t j l≤N j*w j)→(∀j,θ*w j≤1)→
      ∀(c:UnitAddCircle×Domain→ℝ),Measurable c→
      ∀(U ell:ℝ),(∀x p,0≤c (x,p)∧c (x,p)≤U)→0<ell→(∀x p,ell≤c (x,p))→
      ∀{ρ:ℝ},0<ρ→ρ<1/2→∀{m W:ℝ}(hm:0<m)(f g0:EllipticField m W),
      let V:=fun x=>stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun p=>c (x,p)) u
      let D:=fun x l=>NativeClippedHaarDirection.column hm f g0 σ target (fun i=>a i+x) u Λ l
      let Q:=fun x=>∑'l:HaarNode,scoreVariance (V x) (D x l)
      (∀x l,D x l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (V x)).range) ∧
      (∀x,Summable (fun l:HaarNode=>scoreVariance (V x) (D x l))) ∧
      Integrable Q haarAddCircle ∧
      (∫x,Q x ∂haarAddCircle)≤(g:ℝ)*∑j:Fin g,
        ((max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2))*K*sqrt (N j)*sqrt (w j)*
          (signedHeatSqConstant 1 ρ m W*StepInput.negativeEnergy 1 Λ ρ (f.1-g0.1)*
            (Λ^ρ*(θ*w j)^(-(1/2:ℝ))+(θ*w j)^(-(1/2:ℝ)-ρ))):=by
  obtain ⟨h,K,θ,hh,hh1,hK,hθ,htrace⟩:=StoppedDefectBlockHaarTrace.trace n
  refine ⟨h,K,θ,hh,hh1,hK,hθ,?_⟩
  intro g hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper M A hA
    hlo hlohi hM hratio hstlo hsthi hsep w N hw hN htwlo htwhi hθw c hc U ell hcb hell hcl
    ρ hρ hρhalf m W hm f g0 V D Q
  let act:∀j i,u<groupData label rep σ j i:=fun j i=>by
    have hs:=(groupData_bounds label rep hrep σ (fun j=>u+lower j)
      (fun j=>u+upper j) hstlo hsthi j i).1
    linarith [hlo j]
  have act0(i:Fin n):u<σ i:=by linarith [hstlo i,hlo (label i)]
  let B:=fun (j:Fin g) (x:UnitAddCircle) (l:HaarNode)=>meanDirection
    (StoppedDefectBlockProjection.synthesis label rep σ target (fun i=>a i+x) u Λ t hage act j)
      (globalSignedColumn l f.1 g0.1)
  let Qb:=fun (j:Fin g) (x:UnitAddCircle)=>∑'l:HaarNode,scoreVariance (V x) (B j x l)
  have he(x:UnitAddCircle)(l:HaarNode):D x l=∑j:Fin g,B j x l:=by
    rw [←NativeHaarBlockDirections.sum_blocks label (D x l)]
    exact Finset.sum_congr rfl (fun j _=>
      NativeHaarBlockDirections.clipped hm f g0 label rep σ target (fun i=>a i+x)
        u Λ t ht hage act0 act j l)
  have hblocks(x:UnitAddCircle)(j:Fin g):
      (∀l,B j x l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (V x)).range) ∧
      Summable (fun l:HaarNode=>scoreVariance (V x) (B j x l)):=by
    have hb:=StoppedDefectBlockBoundedTrace.trace hg label rep hrep σ target (fun i=>a i+x)
      u Λ hΛ t hage hages lower upper M A hA hlo hlohi hM hratio hstlo hsthi hsep
      (fun p=>c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb x) hell
      (hcl x) j f.1 g0.1 m W hm f.2.1 g0.2.1 f.2.2 g0.2.2
    exact ⟨hb.1,hb.2.1⟩
  have hVp(x:UnitAddCircle):(V x).PosSemidef:=
    StoppedCovarianceSplit.covariance_posSemidef σ target (nativeCenter (fun i=>a i+x)) hages u
      (hc.comp (measurable_const.prodMk measurable_id)) (hcb x)
  have hfull(x:UnitAddCircle):
      (∀l,D x l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (V x)).range) ∧
      Summable (fun l:HaarNode=>scoreVariance (V x) (D x l)) ∧
      Q x≤(g:ℝ)*(∑j:Fin g,Qb j x):=by
    have hh:=FiniteHaarScoreTrace.trace (V x) (hVp x) (fun j l=>B j x l)
      (fun j l=>(hblocks x j).1 l) (fun j=>(hblocks x j).2)
    refine ⟨?_,?_,?_⟩
    · intro l
      rw [he x l]
      exact hh.1 l
    · have heq:(fun l:HaarNode=>scoreVariance (V x) (D x l))=
          fun l:HaarNode=>scoreVariance (V x) (∑j:Fin g,B j x l):=by
        funext l
        rw [he x l]
      rw [heq]
      exact hh.2.1
    · change (∑'l:HaarNode,scoreVariance (V x) (D x l))≤_
      have heq:(fun l:HaarNode=>scoreVariance (V x) (D x l))=
          fun l:HaarNode=>scoreVariance (V x) (∑j:Fin g,B j x l):=by
        funext l
        rw [he x l]
      rw [heq]
      exact hh.2.2
  have hi(j:Fin g):Integrable (Qb j) haarAddCircle:=
    (htrace hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper M A hA
      hlo hlohi hM hratio hstlo hsthi hsep j (w j) (N j) (hw j) (hN j) (htwlo j) (htwhi j) (hθw j)
      c hc U ell hcb hell hcl hρ hρhalf f.1 g0.1 m W hm f.2.1 g0.2.1 f.2.2 g0.2.2 act).1
  have hmass(j:Fin g):(∫x,Qb j x ∂haarAddCircle)≤
      ((max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2))*K*sqrt (N j)*sqrt (w j)*
        (signedHeatSqConstant 1 ρ m W*StepInput.negativeEnergy 1 Λ ρ (f.1-g0.1)*
          (Λ^ρ*(θ*w j)^(-(1/2:ℝ))+(θ*w j)^(-(1/2:ℝ)-ρ))):=
    (htrace hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper M A hA
      hlo hlohi hM hratio hstlo hsthi hsep j (w j) (N j) (hw j) (hN j) (htwlo j) (htwhi j) (hθw j)
      c hc U ell hcb hell hcl hρ hρhalf f.1 g0.1 m W hm f.2.1 g0.2.1 f.2.2 g0.2.2 act).2
  have hVm:Measurable V:=by
    have hm:=translated_feature_gram_measurable σ target a hages u hc U hcb
    convert! hm using 1
    funext x
    exact (weightedFeature_gram σ target (nativeCenter (fun i=>a i+x)) (fun p=>c (x,p))
      (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u).symm
  have hDm(l:HaarNode):Measurable (fun x:UnitAddCircle=>D x l):=by
    have hm:Measurable (fun x:UnitAddCircle=>∑j:Fin g,B j x l):=
      Finset.measurable_sum _ (fun j _=>TranslatedHaarBlockFields.direction label rep σ target a u Λ
        t ht hage act j true (globalSignedColumn l f.1 g0.1))
    have heq:(fun x:UnitAddCircle=>D x l)=fun x:UnitAddCircle=>∑j:Fin g,B j x l:=funext (fun x=>he x l)
    exact (congrArg Measurable heq).mpr hm
  have hQm:Measurable Q:=by
    exact HaarScoreTraceFields.measurable V D hVm hDm
  have hQi:Integrable Q haarAddCircle:=
    ((integrable_finsetSum _ (fun j _=>hi j)).const_mul (g:ℝ)).mono' hQm.aestronglyMeasurable
      (ae_of_all _ (fun x=>by
        rw [Real.norm_of_nonneg (tsum_nonneg (fun l=>scoreVariance_nonneg (hVp x) ((hfull x).1 l)))]
        exact (hfull x).2.2))
  refine ⟨fun x=>(hfull x).1,fun x=>(hfull x).2.1,hQi,?_⟩
  calc
    _≤∫x,(g:ℝ)*(∑j:Fin g,Qb j x) ∂haarAddCircle:=integral_mono hQi
      ((integrable_finsetSum _ (fun j _=>hi j)).const_mul _) (fun x=>(hfull x).2.2)
    _=(g:ℝ)*(∑j:Fin g,∫x,Qb j x ∂haarAddCircle):=by
      rw [integral_const_mul,integral_finsetSum _ (fun j _=>hi j)]
    _≤_:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _=>hmass j)) (by positivity)

end SHE.StoppedFullSignedHaarTrace
