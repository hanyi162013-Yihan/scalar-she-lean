module
public import SHE.LeftFrozenHaarConsistency
public import SHE.FixedHaarIntegral
public import SHE.PredictableSteps
public import SHE.ContinuousPredictable
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.LeftFrozenHaarInput
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand LeftFrozenHaarKernel
open ApproximationCells
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable {a:ℝ→ℝ}(ha:Measurable a){ell M Holder β:ℝ}(hell:0<ell)
variable(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hHolder:0≤Holder)
variable(hholder:∀z w,|a z-a w|≤Holder*|z-w|^β)
variable(U:ℝ≥0→Ω→StateL2)(hUa:StronglyAdapted 𝓕 U)

def coefficient(n:ℕ)(t:ℝ≥0)(k:ℕ)(ω:Ω):RealHaarIntegrand.Columns:=
  if point n (k-1)<t then kernel a ha ell M hell hb
    ((t:ℝ)-(point n (k-1):ℝ),U (point n (k-1)) ω) else 0

def bound(n:ℕ)(t:ℝ≥0)(k:ℕ):ℝ:=
  Real.sqrt (M*(1+2*HeatTrace.fractionalGaussianIntegral 0*
    ((t:ℝ)-(point n (k-1):ℝ))^(-(1/2:ℝ))))

include hβ hHolder hholder hUa in
theorem coefficient_adapted(n:ℕ)(t:ℝ≥0)(k:ℕ):
    StronglyMeasurable[𝓕 (point n (k-1))] (coefficient ha hell hb U n t k):=by
  unfold coefficient
  split_ifs
  · exact ((kernel_measurable ha hell hb hβ hHolder hholder).comp
      (measurable_const.prodMk (hUa (point n (k-1))).measurable)).stronglyMeasurable
  · exact stronglyMeasurable_const

theorem coefficient_bound(n:ℕ)(t:ℝ≥0)(k:ℕ)(ω:Ω):
    ‖coefficient ha hell hb U n t k ω‖≤bound (M:=M) n t k:=by
  have hM:0≤M:=hell.le.trans ((hb 0).1.trans (hb 0).2)
  have hG:0≤HeatTrace.fractionalGaussianIntegral 0:=
    (HeatTrace.fractionalGaussianIntegral_pos (by norm_num:(0:ℝ)<1/2)).le
  unfold coefficient
  split_ifs with ht
  · have hage:0<(t:ℝ)-(point n (k-1):ℝ):=
      sub_pos.mpr (by exact_mod_cast ht)
    have hB:0≤M*(1+2*HeatTrace.fractionalGaussianIntegral 0*
        ((t:ℝ)-(point n (k-1):ℝ))^(-(1/2:ℝ))):=
      mul_nonneg hM (add_nonneg zero_le_one
        (mul_nonneg (mul_nonneg (by norm_num) hG) (Real.rpow_nonneg hage.le _)))
    have he:=kernel_norm_sq_bound ha hell hb hage (U (point n (k-1)) ω)
    dsimp only [bound]
    exact (Real.le_sqrt (norm_nonneg _) hB).mpr he
  · simpa only [norm_zero,bound] using Real.sqrt_nonneg (M*(1+2*HeatTrace.fractionalGaussianIntegral 0*
      ((t:ℝ)-(point n (k-1):ℝ))^(-(1/2:ℝ))))

include hβ hHolder hholder hUa in
theorem coefficient_memLp(n:ℕ)(t:ℝ≥0)(k:ℕ):
    MemLp (coefficient ha hell hb U n t k) 2 μ:=by
  apply MemLp.of_bound
    ((coefficient_adapted 𝓕 ha hell hb hβ hHolder hholder U hUa n t k).mono
      (𝓕.le _)).aestronglyMeasurable (bound (M:=M) n t k)
  exact ae_of_all _ (coefficient_bound ha hell hb U n t k)

def cell(n:ℕ)(t:ℝ≥0)(k:ℕ):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  PredictableSteps.process 𝓕 μ H (point n (k-1)) (min (point n k) t)
    (coefficient ha hell hb U n t k)
    (coefficient_adapted 𝓕 ha hell hb hβ hHolder hholder U hUa n t k)
    (coefficient_memLp 𝓕 μ ha hell hb hβ hHolder hholder U hUa n t k)

def input(n:ℕ)(t:ℝ≥0):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  ∑k∈Finset.Icc 1 (index n t),cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k

theorem raw_sum_eq(n:ℕ)(t s:ℝ≥0)(ω:Ω)(hs:0<s)(hne:s≠t):
    (∑k∈Finset.Icc 1 (index n t),PredictableSteps.step (point n (k-1))
      (min (point n k) t) (coefficient ha hell hb U n t k) (s,ω))=
    value ha hell hb U n (t,(s,ω)):=by
  by_cases hst:s<t
  · have hst':s≤t:=hst.le
    have he:(∑k∈Finset.Icc 1 (index n t),PredictableSteps.step (point n (k-1))
        (min (point n k) t) (coefficient ha hell hb U n t k) (s,ω))=
        ApproximationCells.sum n t (coefficient ha hell hb U n t) (s,ω):=by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [PredictableSteps.step,ApproximationCells.sum,mem_Ioc,le_min_iff,hst',and_true]
    rw [he,ApproximationCells.sum_at n hs hst' _ ω]
    have hp:past n s=point n (index n s-1):=by
      apply NNReal.coe_injective
      rw [past,Real.coe_toNNReal _ (ApproximationClock.left_bounds n (show 0<(s:ℝ) from hs)).1,
        left_eq_point n hs]
    have hpt:point n (index n s-1)<t:=by rw [←hp];exact (past_le n s).trans_lt hst
    simp only [coefficient,ite_eq_left hpt,value,ite_eq_left hst,hp]
  · have hts:t<s:=lt_of_le_of_ne (le_of_not_gt hst) hne.symm
    rw [Finset.sum_eq_zero]
    · simp only [value,ite_eq_right hst]
    · intro k hk
      exact if_neg (fun hm=>not_le.mpr hts (hm.2.trans (min_le_right _ _)))

theorem input_ae(n:ℕ)(t:ℝ≥0):
    input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t=ᵐ[energyMeasure μ H]
      (fun p=>value ha hell hb U n (t,p)):=by
  have hsum:=ae_eq_of_ae_eq_trim (Lp.coeFn_fun_finsetSum (Finset.Icc 1 (index n t))
    (fun k=>cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k))
  have hcells:∀ᵐp∂energyMeasure μ H,∀k:ℕ,
      cell 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t k p=
        PredictableSteps.step (point n (k-1)) (min (point n k) t)
          (coefficient ha hell hb U n t k) p:=by
    apply ae_all_iff.mpr
    intro k
    exact PredictableSteps.process_ae 𝓕 μ H _ _ _ _ _
  have hpos:∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,0<p.1:=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem H).mono (fun s hs=>hs.1))
  have hne:∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,p.1≠t:=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne t)
  filter_upwards [hsum,hcells,hpos,hne] with p hsum hcells hp hne
  exact hsum.trans ((Finset.sum_congr rfl (fun k _=>hcells k)).trans
    (raw_sum_eq ha hell hb U n t p.1 p.2 hp hne))
end SHE.LeftFrozenHaarInput
