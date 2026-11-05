module

public import SHE.NormalizedScalarMoment
public import SHE.OwnBaselineTelescope

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.PhysicalNormalizedAssignedPair
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  StoppedGaussianFeatures StoppedFourier ProfileVariance
open scoped BigOperators
local instance physicalNormalizedAssignedPair_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n r k : ℕ}

/-- A nonempty paired rough block, normalized by its actual current
increment BEFORE Gaussian integration, has the complementary old-gap
power uniformly in every current mean and both original baselines. -/
theorem even_moment (P : CanonicalCovariance.ProfileParameters)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (c : Domain→ℝ) (hc : Measurable c) {M : ℝ} (hcb : ∀ z,0≤c z ∧ c z≤M)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,0≤lo j) (hgap : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i) (B : Matrix (Fin n) (Fin n) ℝ)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (j : Fin r) (hchosen : j∈block choices factor) (i : Fin n)
    (newMean oldMean : State n) (newBaseline oldBaseline : ℝ)
    {χ : ℝ} (hχ : 0≤χ) (hχβ : χ≤P.exponent) (p : ℕ) (hp : 0<p) :
    let A:=OldIntervalCovariance.familyCovariance σ target center c lo hi
    let ν:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let source:=|newMean i-oldMean i|^χ
    let N:=fun x=>NormalizedScalarMoment.value
      (ControlledAssignedLeaf.leaf choices factor P.coefficient newMean i newBaseline x-
        ControlledAssignedLeaf.leaf choices factor P.coefficient oldMean i oldBaseline x) source
    Integrable (fun x=>|N x|^(2*p)) ν ∧
      (∫ x,|N x|^(2*p) ∂ν)≤GaussianAudit.gaussianAbsMoment (((2*p:ℕ):ℝ)*(P.exponent-χ))*
        ((2:ℝ)^((block choices factor).length)*P.holder*
          (upperConstant*M)^((P.exponent-χ)/2)*(hi j-lo j)^((P.exponent-χ)/4))^(2*p) := by
  intro A ν source N
  have hblock : block choices factor≠[]:=List.ne_nil_of_mem hchosen
  have he:=OwnBaselineTelescope.leaf_nonempty_difference choices factor hblock P.coefficient
    newMean oldMean i newBaseline oldBaseline
  have hh:=PhysicalPairedRough.even_moment σ target center hσ hσ1 hages c hc hcb lo hi hlo hgap hstop
    B choices hnd factor j hchosen i P.coefficient P.measurable P.holder_nonneg hχ hχβ
    P.holder_bound (fun y=>oldMean i+y i) (by fun_prop) (newMean i-oldMean i) p
  dsimp only at hh
  rw [←he] at hh
  let S:=(2:ℝ)^((block choices factor).length)*P.holder*
    (upperConstant*M)^((P.exponent-χ)/2)*(hi j-lo j)^((P.exponent-χ)/4)
  have hM : 0≤M:=(hcb (0,0)).1.trans (hcb (0,0)).2
  have hS : 0≤S:=by
    dsimp [S]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) P.holder_nonneg)
      (rpow_nonneg (mul_nonneg upperConstant_pos.le hM) _))
        (rpow_nonneg (sub_pos.mpr (hgap j)).le _)
  have hsrc : 0≤source:=rpow_nonneg (abs_nonneg _) _
  have hScale : (2:ℝ)^((block choices factor).length)*P.holder*|newMean i-oldMean i|^χ*
      (upperConstant*M)^((P.exponent-χ)/2)*(hi j-lo j)^((P.exponent-χ)/4)=source*S := by
    dsimp [source,S]
    ring
  rw [hScale] at hh
  exact NormalizedScalarMoment.even_moment ν _ p hp hsrc
    (GaussianAudit.gaussianAbsMoment_nonneg _) hS hh.1 hh.2

/-- Exact factorization retains the real current input outside every
conditional Gaussian expectation, even when that current increment is zero. -/
theorem factorization (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (j : Fin r) (hchosen : j∈block choices factor) (i : Fin n)
    (newMean oldMean : State n) (newBaseline oldBaseline : ℝ)
    {χ : ℝ} (hχ : 0≤χ) (hχβ : χ≤P.exponent) (x : (Fin r→State n)×State n) :
    |newMean i-oldMean i|^χ*NormalizedScalarMoment.value
      (ControlledAssignedLeaf.leaf choices factor P.coefficient newMean i newBaseline x-
        ControlledAssignedLeaf.leaf choices factor P.coefficient oldMean i oldBaseline x)
      (|newMean i-oldMean i|^χ)=
        ControlledAssignedLeaf.leaf choices factor P.coefficient newMean i newBaseline x-
          ControlledAssignedLeaf.leaf choices factor P.coefficient oldMean i oldBaseline x := by
  apply NormalizedScalarMoment.factorization
  intro hzero
  have hb:=PairedRoughBlocks.value_interpolated_bound choices hnd factor j hchosen P.coefficient
    P.holder_nonneg hχ hχβ P.holder_bound (fun y=>oldMean i+y i)
    (fun _ : Fin r=>EuclideanSpace.proj (𝕜:=ℝ) i) (newMean i-oldMean i) x
  rw [←OwnBaselineTelescope.leaf_nonempty_difference choices factor (List.ne_nil_of_mem hchosen)
    P.coefficient newMean oldMean i newBaseline oldBaseline] at hb
  rw [hzero,mul_zero,zero_mul] at hb
  exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))

end SHE.PhysicalNormalizedAssignedPair
