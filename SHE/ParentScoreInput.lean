module

public import SHE.ForestedScoreInput
public import SHE.ParentHeatForests
public import SHE.ForestTranslation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ForestedScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 StoppedScoreLeverage StoppedCovarianceInput OrderedHeatForests
open scoped BigOperators
local instance parentScoreInput_periodPos : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

theorem parentDensity_continuous {m : ℕ} (κ : ℝ) (hκ : 0<κ) (k : ℕ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) : Continuous (parentDensity κ hκ k t ht) := by
  have he : parentDensity κ hκ k t ht=
      fun z=>∑ Q : Choices m k,density (ofChoices κ hκ k t ht Q) z := by
    funext z
    exact (sum_density_eq κ hκ k t ht z).symm
  rw [he]
  exact continuous_finset_sum _ (fun Q _=>density_continuous _)

theorem parentDensity_mass {m : ℕ} (κ : ℝ) (hκ : 0<κ) (k : ℕ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin m→HeatCircle) :
    (∫ w : Fin k→HeatCircle,parentDensity κ hκ k t ht (values aRoot k w)
      ∂Measure.pi (fun _=>haarAddCircle))=(Fintype.card (Choices m k):ℝ) := by
  simp_rw [←sum_density_eq κ hκ k t ht]
  rw [integral_finset_sum]
  · have hm (Q : Choices m k) :
        (∫ w : Fin k→HeatCircle,density (ofChoices κ hκ k t ht Q) (values aRoot k w)
          ∂Measure.pi (fun _=>haarAddCircle))=1 := by
      simpa only [average_const,mul_one] using
        (average_eq_integral_continuous (ofChoices κ hκ k t ht Q) (fun _=>1) continuous_const aRoot).symm
    simp only [hm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  · intro Q _
    exact ((density_continuous _).comp (values_continuous aRoot k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The literal product of every old parent heat sum costs only the
finite forest count. No additional small-time loss is introduced by the
one-input covariance transfer. -/
theorem parent_input_normTwo {m k : ℕ} (κ : ℝ) (hκ : 0<κ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin m→HeatCircle)
    (σ target : Fin (m+k)→ℝ)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {s α τ ell U A B : ℝ} (hs : 0<s) (hα : -1<α) (hα0 : α≤0)
    (hτ : -1<τ) (hτ0 : τ<0) (hell : 0<ell) (hA : 0≤A) (hB : 0≤B)
    (hstop : ∀ i,s≤σ i) (c e : Domain→ℝ) (hc : Measurable c) (he : Measurable e)
    (hcb : ∀ p,0≤c p ∧ c p≤U) (hcl : ∀ p,ell≤c p)
    (hcoarse : ∀ p,0≤p.1 → |e p|≤B*p.1^τ)
    (hsharp : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),normTwo haarAddCircle (fun x=>e (r,x))≤A*r^α) :
    normTwo haarAddCircle (fun x=>∫ w : Fin k→HeatCircle,
      parentDensity κ hκ k t ht (values aRoot k w)*scoreInput σ target (values aRoot k w) c e x
        ∂Measure.pi (fun _=>haarAddCircle))≤
      (Fintype.card (Choices m k):ℝ)*(A*(((m+k:ℕ):ℝ)/ell*(s/2)^α*(1+2/(α+1)))) := by
  have hKc := (parentDensity_continuous κ hκ k t ht).comp (values_continuous aRoot k)
  have hKi : Integrable (fun w : Fin k→HeatCircle=>parentDensity κ hκ k t ht (values aRoot k w))
      (Measure.pi (fun _=>haarAddCircle)) :=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK (w : Fin k→HeatCircle) : 0≤parentDensity κ hκ k t ht (values aRoot k w) := by
    rw [←sum_density_eq κ hκ k t ht]
    exact Finset.sum_nonneg (fun Q _=>density_nonneg _ _)
  have hh := averaged_input_normTwo (Measure.pi (fun _ : Fin k=>haarAddCircle))
    (fun w=>parentDensity κ hκ k t ht (values aRoot k w)) hKc.measurable hKi hK
    σ target (values aRoot k) (values_continuous aRoot k).measurable hσ hσ1 hages hs hα hα0 hτ hτ0
    hell hA hB hstop c e hc he hcb hcl hcoarse hsharp
  simpa only [parentDensity_mass] using hh

end SHE.ForestedScoreInput
