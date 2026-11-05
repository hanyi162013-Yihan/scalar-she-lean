module
public import SHE.FiniteHaarScoreTrace
public import SHE.NativeHaarBlockDirections
public import SHE.StoppedDefectBlockBoundedTrace
public import SHE.StoppedCovarianceSplit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.StoppedFullHaarTrace
open Set MeasureTheory Real AddCircle FiniteHaar CircleHeat StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores BlockDefectScores CommonHaarDefectTrace
local instance : Fact (0<2*π):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {n g:ℕ}(hg:0<g)(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (hrep:∀j,label (rep j)=j)(σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)(hΛ:0<Λ)
    (t:Fin n→ℝ)(ht:∀i,0<t i)(hage:∀i,target i-u=4*π^2*t i)(hages:∀i,σ i≤target i)
    (lower upper R:Fin g→ℝ)(A:ℝ)(hA:4*(g:ℝ)^2+1≤A)
    (hlo:∀j,0<lower j)(hlohi:∀j,lower j≤upper j)(hR:∀j,1≤R j)
    (hratio:∀j,upper j≤R j*lower j)
    (hstlo:∀i,u+lower (label i)≤σ i)(hsthi:∀i,σ i≤u+upper (label i))
    (hsep:∀j k,j<k→A*upper j≤lower k)
    (c:Domain→ℝ)(hc:Measurable c)(U ell:ℝ)(hcb:∀p,0≤c p ∧ c p≤U)
    (hell:0<ell)(hcl:∀p,ell≤c p)
    {m W:ℝ}(hm:0<m)(f g0:EllipticField m W)
local notation "V"=>stoppedCovariance σ target (nativeCenter a) c u
local notation "D"=>NativeClippedHaarDirection.column hm f g0 σ target a u Λ
local notation "Wr"=>direction (fun i=>NativeObservationCovariance.row hm g0 (target i) u (nativeCenter a i))
include hg hrep hΛ ht hage hages hA hlo hlohi hR hratio hstlo hsthi hsep hc hcb hell hcl

/-- Every original clipped Haar direction is scored in the ORIGINAL
full covariance. The finite block sum preserves range and summability. -/
theorem clipped:
    (∀l:HaarNode,D l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) V).range) ∧
      Summable (fun l:HaarNode=>scoreVariance V (D l)) ∧
      (∑'l:HaarNode,scoreVariance V (D l))≤
        (g:ℝ)*(∑j:Fin g,((max (R j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2))*(4*W*(n:ℝ))):=by
  have act:∀i,u<σ i:=by intro i;linarith [hlo (label i),hstlo i]
  let actg:∀j i,u<groupData label rep σ j i:=fun j i=>by
    have hp:=(groupData_bounds label rep hrep σ (fun j=>u+lower j)
      (fun j=>u+upper j) hstlo hsthi j i).1
    linarith [hlo j]
  have hb(j:Fin g):=StoppedDefectBlockBoundedTrace.trace hg label rep hrep σ target a u Λ hΛ
    t hage hages lower upper R A hA hlo hlohi hR hratio hstlo hsthi hsep c hc U ell hcb hell hcl j
    f.1 g0.1 m W hm f.2.1 g0.2.1 f.2.2 g0.2.2
  have he(j:Fin g)(l:HaarNode):restrictCoefficients label j (D l)=
      meanDirection (StoppedDefectBlockProjection.synthesis label rep σ target a u Λ t hage actg j)
        (globalSignedColumn l f.1 g0.1):=
    NativeHaarBlockDirections.clipped hm f g0 label rep σ target a u Λ t ht hage act actg j l
  have hr:∀j l,restrictCoefficients label j (D l)∈(Matrix.toEuclideanCLM (𝕜:=ℝ) V).range:=by
    intro j l
    rw [he j l]
    exact (hb j).1 l
  have hs(j:Fin g):Summable (fun l:HaarNode=>scoreVariance V (restrictCoefficients label j (D l))):=by
    simp_rw [he j]
    exact (hb j).2.1
  have hV:(V).PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef σ target (nativeCenter a) hages u hc hcb
  have h:=FiniteHaarScoreTrace.trace V hV (fun j l=>restrictCoefficients label j (D l)) hr hs
  simp_rw [NativeHaarBlockDirections.sum_blocks] at h
  refine ⟨h.1,h.2.1,h.2.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg g)
  apply Finset.sum_le_sum
  intro j _
  simp_rw [he j]
  exact (hb j).2.2

/-- The companion current Haar row is kept in the same original full
covariance and combined only after each true block trace is proved. -/
theorem current:
    (∀l:HaarNode,Wr l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) V).range) ∧
      Summable (fun l:HaarNode=>scoreVariance V (Wr l)) ∧
      (∑'l:HaarNode,scoreVariance V (Wr l))≤
        (g:ℝ)*(∑j:Fin g,((2/lower j)/(ell/2))*W*(n:ℝ)):=by
  let actg:∀j i,u<groupData label rep σ j i:=fun j i=>by
    have hp:=(groupData_bounds label rep hrep σ (fun j=>u+lower j)
      (fun j=>u+upper j) hstlo hsthi j i).1
    linarith [hlo j]
  have hb(j:Fin g):=StoppedCurrentBlockHaarTrace.trace hg label rep hrep σ target a u
    t hage hages lower upper A hA hlo hlohi hstlo hsthi hsep c hc U ell hcb hell hcl j
    g0.1 m W hm g0.2.1 g0.2.2
  have he(j:Fin g)(l:HaarNode):restrictCoefficients label j (Wr l)=
      meanDirection (StoppedCurrentBlockHaarTrace.synthesis label rep σ target a u t hage actg j)
        (globalHaarColumn l g0.1):=
    NativeHaarBlockDirections.current hm g0 label rep σ target a u t ht hage actg j l
  have hr:∀j l,restrictCoefficients label j (Wr l)∈(Matrix.toEuclideanCLM (𝕜:=ℝ) V).range:=by
    intro j l
    rw [he j l]
    exact (hb j).1 l
  have hs(j:Fin g):Summable (fun l:HaarNode=>scoreVariance V (restrictCoefficients label j (Wr l))):=by
    simp_rw [he j]
    exact (hb j).2.1
  have hV:(V).PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef σ target (nativeCenter a) hages u hc hcb
  have h:=FiniteHaarScoreTrace.trace V hV (fun j l=>restrictCoefficients label j (Wr l)) hr hs
  simp_rw [NativeHaarBlockDirections.sum_blocks] at h
  refine ⟨h.1,h.2.1,h.2.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg g)
  apply Finset.sum_le_sum
  intro j _
  simp_rw [he j]
  exact (hb j).2.2

end SHE.StoppedFullHaarTrace
