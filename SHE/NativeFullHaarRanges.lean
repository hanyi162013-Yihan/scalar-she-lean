module

public import SHE.StoppedFullHaarTrace
public import SHE.AgePartition

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace SHE.NativeFullHaarRanges
open Set MeasureTheory Real AddCircle FiniteHaar StoppedFourier StoppedGaussianScore
  StoppedGaussianFeatures GaussianIncrement MeasurableGaussianScores CommonHaarDefectTrace
open scoped BigOperators
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- Full actual clipped/current Haar directions belong to the SAME
original stopped covariance range, for arbitrary positive native ages.
The deterministic age partition is used only inside this proof. -/
theorem ranges {n:ℕ}(hn:0<n)(target:Fin n→ℝ)(a:Fin n→AddCircle (1:ℝ))(q Λ:ℝ)
    (hΛ:0<Λ)(hgap:∀i,q<target i)(c:Domain→ℝ)(hc:Measurable c)
    (U ell:ℝ)(hcb:∀p,0≤c p ∧ c p≤U)(hell:0<ell)(hcl:∀p,ell≤c p)
    {m W:ℝ}(hm:0<m)(f g:EllipticField m W):
    let V:=stoppedCovariance target target (nativeCenter a) c q
    let D:=NativeClippedHaarDirection.column hm f g target target a q Λ
    let Wr:=direction (fun i=>NativeObservationCovariance.row hm g (target i) q (nativeCenter a i))
    (∀l:HaarNode,D l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) V).range) ∧
      Summable (fun l:HaarNode=>scoreVariance V (D l)) ∧
      (∀l:HaarNode,Wr l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) V).range) ∧
      Summable (fun l:HaarNode=>scoreVariance V (Wr l)):=by
  intro V D Wr
  let A:ℝ:=4*(n:ℝ)^2+1
  have hA:1≤A:=by dsimp [A];nlinarith [sq_nonneg (n:ℝ)]
  obtain ⟨P⟩:=AgeClustering.exists_partition (fun i=>target i-q) (fun i=>sub_pos.mpr (hgap i)) hA
  have hg:=P.count_pos hn
  have hPA:4*(P.count:ℝ)^2+1≤A:=by
    have hh:(P.count:ℝ)≤n:=by exact_mod_cast P.count_le
    dsimp [A]
    nlinarith [show (0:ℝ)≤(P.count:ℝ) by positivity]
  let t:=fun i:Fin n=>(target i-q)/(4*Real.pi^2)
  have ht:∀i,0<t i:=fun i=>div_pos (sub_pos.mpr (hgap i)) (by positivity)
  have hage:∀i,target i-q=4*Real.pi^2*t i:=by
    intro i
    dsimp only [t]
    field_simp
  have hlo:∀i,q+P.lower (P.label i)≤target i:=fun i=>by linarith [P.lower_bound i]
  have hhi:∀i,target i≤q+P.upper (P.label i):=fun i=>by linarith [P.upper_bound i]
  have hM:∀_:Fin P.count,1≤A^n:=fun _=>one_le_pow₀ hA
  have hD:=StoppedFullHaarTrace.clipped hg P.label P.rep P.label_rep target target a q Λ hΛ
    t ht hage (fun _=>le_rfl) P.lower P.upper (fun _=>A^n) A hPA P.lower_pos P.lower_le_upper
    hM P.ratio hlo hhi P.separation c hc U ell hcb hell hcl hm f g
  have hW:=StoppedFullHaarTrace.current hg P.label P.rep P.label_rep target target a q Λ hΛ
    t ht hage (fun _=>le_rfl) P.lower P.upper (fun _=>A^n) A hPA P.lower_pos P.lower_le_upper
    hM P.ratio hlo hhi P.separation c hc U ell hcb hell hcl hm g
  exact ⟨hD.1,hD.2.1,hW.1,hW.2.1⟩

end SHE.NativeFullHaarRanges
