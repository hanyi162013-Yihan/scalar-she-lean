module

public import SHE.StoppedFullSignedHaarTrace
public import SHE.StoppedFullHaarTrace
public import SHE.HaarDefectSpatialEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.StoppedFullDefectSpatial
open Set MeasureTheory Real AddCircle FiniteHaar CircleHeat StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores CommonHaarDefectTrace
open scoped BigOperators
local instance : Fact (0<2*π):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- The full two-cross-plus-quadratic physical packet has a genuine
root L2 bound. Both covariance slots keep their own actual profile,
and every direction is scored in its ORIGINAL full covariance. -/
theorem energy (n:ℕ):
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
      ∀(cR cC:UnitAddCircle×Domain→ℝ),Measurable cR→Measurable cC→
      ∀(U ell:ℝ),(∀x p,0≤cR (x,p)∧cR (x,p)≤U)→
      (∀x p,0≤cC (x,p)∧cC (x,p)≤U)→0<ell→
      (∀x p,ell≤cR (x,p))→(∀x p,ell≤cC (x,p))→
      ∀{ρ:ℝ},0<ρ→ρ<1/2→∀{m W:ℝ}(hm:0<m)(hW:0≤W)(f g0:EllipticField m W),
      let R:=fun x=>stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun p=>cR (x,p)) u
      let C:=fun x=>stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun p=>cC (x,p)) u
      let D:=fun x l=>NativeClippedHaarDirection.column hm f g0 σ target (fun i=>a i+x) u Λ l
      let Wr:=fun x=>direction (fun i=>NativeObservationCovariance.row hm g0 (target i) u
        (nativeCenter (fun i=>a i+x) i))
      let aR:=fun x=>∑'l:HaarNode,scoreVariance (R x) (D x l)
      let aC:=fun x=>∑'l:HaarNode,scoreVariance (C x) (D x l)
      let bR:=fun x=>∑'l:HaarNode,scoreVariance (R x) (Wr x l)
      let bC:=fun x=>∑'l:HaarNode,scoreVariance (C x) (Wr x l)
      let EB:=(g:ℝ)*∑j:Fin g,((max (M j) 8*(lower j)⁻¹)/(ell/2))*(4*W*(n:ℝ))
      let EA:=(g:ℝ)*∑j:Fin g,
        ((max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2))*K*sqrt (N j)*sqrt (w j)*
          (signedHeatSqConstant 1 ρ m W*StepInput.negativeEnergy 1 Λ ρ (f.1-g0.1)*
            (Λ^ρ*(θ*w j)^(-(1/2:ℝ))+(θ*w j)^(-(1/2:ℝ)-ρ)))
      ∀(F f₁ f₂ f₃:UnitAddCircle→ℝ),Measurable F→∀G:ℝ,0≤G→
      (∀x,F x=(f₁ x+f₂ x+f₃ x)/2)→
      (∀ᵐx∂haarAddCircle,
        |f₁ x|≤G*(sqrt (aR x)*sqrt (bC x)) ∧
        |f₂ x|≤G*(sqrt (bR x)*sqrt (aC x)) ∧
        |f₃ x|≤G*(sqrt (aR x)*sqrt (aC x)))→
      Integrable (fun x=>|F x|^2) haarAddCircle ∧
        (∫x,|F x|^2 ∂haarAddCircle)≤(9/4:ℝ)*G^2*EB*EA:=by
  obtain ⟨h,K,θ,hh,hh1,hK,hθ,htrace⟩:=StoppedFullSignedHaarTrace.integral n
  refine ⟨h,K,θ,hh,hh1,hK,hθ,?_⟩
  intro g hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper M A hA
    hlo hlohi hM hratio hstlo hsthi hsep w N hw hN htwlo htwhi hθw cR cC hcR hcC U ell
    hRb hCb hell hRl hCl ρ hρ hρhalf m W hm hW f g0 R C D Wr aR aC bR bC EB EA
    F f₁ f₂ f₃ hF G hG he hp
  have hR:=htrace hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper M A hA
    hlo hlohi hM hratio hstlo hsthi hsep w N hw hN htwlo htwhi hθw cR hcR U ell hRb hell hRl
    hρ hρhalf hm f g0
  have hC:=htrace hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper M A hA
    hlo hlohi hM hratio hstlo hsthi hsep w N hw hN htwlo htwhi hθw cC hcC U ell hCb hell hCl
    hρ hρhalf hm f g0
  have full(c:UnitAddCircle×Domain→ℝ)(hc:Measurable c)(hcb:∀x p,0≤c (x,p)∧c (x,p)≤U)
      (hcl:∀x p,ell≤c (x,p))(x:UnitAddCircle):
      (∑'l:HaarNode,scoreVariance
        (stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun p=>c (x,p)) u) (Wr x l))≤EB ∧
      (∑'l:HaarNode,scoreVariance
        (stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun p=>c (x,p)) u) (D x l))≤EB:=by
    have hs:=StoppedFullHaarTrace.current hg label rep hrep σ target (fun i=>a i+x) u Λ hΛ
      t ht hage hages lower upper M A hA hlo hlohi hM hratio hstlo hsthi hsep
      (fun p=>c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb x) hell (hcl x) hm g0
    have hd:=StoppedFullHaarTrace.clipped hg label rep hrep σ target (fun i=>a i+x) u Λ hΛ
      t ht hage hages lower upper M A hA hlo hlohi hM hratio hstlo hsthi hsep
      (fun p=>c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb x) hell (hcl x) hm f g0
    have hcst(j:Fin g):((2/lower j)/(ell/2))*W*(n:ℝ)≤
        ((max (M j) 8*(lower j)⁻¹)/(ell/2))*(4*W*(n:ℝ)):=by
      have hdj:=hlo j
      have hmj:2≤4*max (M j) 8:=by have hh:=le_max_right (M j) 8;linarith
      have hh:=mul_le_mul_of_nonneg_right hmj
        (show 0≤((lower j)⁻¹/(ell/2))*W*(n:ℝ) by positivity)
      convert hh using 1 <;> simp only [div_eq_mul_inv] <;> ring
    have hdct(j:Fin g):
        ((max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2))*(4*W*(n:ℝ))≤
        ((max (M j) 8*(lower j)⁻¹)/(ell/2))*(4*W*(n:ℝ)):=by
      have hdj:=hlo j
      have hm0:0≤min 1 (Λ*lower j):=le_min zero_le_one (mul_nonneg hΛ.le (hlo j).le)
      have hm1:min 1 (Λ*lower j)≤1:=min_le_left _ _
      have hs:(min 1 (Λ*lower j))^2≤1:=by nlinarith
      have hh:=mul_le_mul_of_nonneg_right hs
        (show 0≤((max (M j) 8*(lower j)⁻¹)/(ell/2))*(4*W*(n:ℝ)) by positivity)
      convert hh using 1 <;> ring
    exact ⟨hs.2.2.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _=>hcst j)) (by positivity)),
      hd.2.2.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _=>hdct j)) (by positivity))⟩
  have hRp(x:UnitAddCircle):(R x).PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef
    σ target (nativeCenter (fun i=>a i+x)) hages u
    (hcR.comp (measurable_const.prodMk measurable_id)) (hRb x)
  have hCp(x:UnitAddCircle):(C x).PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef
    σ target (nativeCenter (fun i=>a i+x)) hages u
    (hcC.comp (measurable_const.prodMk measurable_id)) (hCb x)
  have hWR(x:UnitAddCircle):=StoppedFullHaarTrace.current hg label rep hrep σ target (fun i=>a i+x) u Λ hΛ
    t ht hage hages lower upper M A hA hlo hlohi hM hratio hstlo hsthi hsep
    (fun p=>cR (x,p)) (hcR.comp (measurable_const.prodMk measurable_id)) U ell (hRb x) hell (hRl x) hm g0
  have hWC(x:UnitAddCircle):=StoppedFullHaarTrace.current hg label rep hrep σ target (fun i=>a i+x) u Λ hΛ
    t ht hage hages lower upper M A hA hlo hlohi hM hratio hstlo hsthi hsep
    (fun p=>cC (x,p)) (hcC.comp (measurable_const.prodMk measurable_id)) U ell (hCb x) hell (hCl x) hm g0
  have haR(x:UnitAddCircle):0≤aR x:=tsum_nonneg (fun l=>scoreVariance_nonneg (hRp x) (hR.1 x l))
  have haC(x:UnitAddCircle):0≤aC x:=tsum_nonneg (fun l=>scoreVariance_nonneg (hCp x) (hC.1 x l))
  have hbR(x:UnitAddCircle):0≤bR x:=tsum_nonneg (fun l=>scoreVariance_nonneg (hRp x) ((hWR x).1 l))
  have hbC(x:UnitAddCircle):0≤bC x:=tsum_nonneg (fun l=>scoreVariance_nonneg (hCp x) ((hWC x).1 l))
  have hEB:0≤EB:=(hbR 0).trans (full cR hcR hRb hRl 0).1
  have hE:=HaarDefectSpatialEnergy.energy haarAddCircle F f₁ f₂ f₃ aR aC bR bC hF hR.2.2.1 hC.2.2.1
    haR haC hG hEB hEB hEB (fun x=>(full cR hcR hRb hRl x).1)
    (fun x=>(full cC hcC hCb hCl x).1) (fun x=>(full cC hcC hCb hCl x).2) he hp hbR hbC
  refine ⟨hE.1,hE.2.trans ?_⟩
  have hr:=mul_le_mul_of_nonneg_left hR.2.2.2 (by positivity:0≤EB+EB)
  have hc:=mul_le_mul_of_nonneg_left hC.2.2.2 hEB
  have hh:=mul_le_mul_of_nonneg_left (add_le_add hr hc) (by positivity:0≤(3/4:ℝ)*G^2)
  convert hh using 1 <;> ring

end SHE.StoppedFullDefectSpatial
