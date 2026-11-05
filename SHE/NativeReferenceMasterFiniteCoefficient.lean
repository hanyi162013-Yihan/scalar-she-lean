module
public import SHE.NativeReferenceMasterCoefficient
public import SHE.PastReferenceConstantUniform
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeReferenceMasterFiniteCoefficient
open MeasureTheory Real
open scoped NNReal ENNReal BigOperators

def constant(Q:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(N p:ℕ)
    (A:Fin N→ℝ)(Babs B0:Fin N→ℝ≥0)(β:ℝ):ℝ:=
  ∑k:Fin N,NativeReferenceMasterCoefficient.constant Q κ M (A k) (k+1) p (Babs k) (B0 k) β

theorem constant_nonneg(Q:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(N p:ℕ)
    (A:Fin N→ℝ)(Babs B0:Fin N→ℝ≥0){β:ℝ}(hβ:0<β)(hβsmall:β≤4/25):
    0≤constant Q κ M N p A Babs B0 β:=
  Finset.sum_nonneg (fun k _=>NativeReferenceMasterCoefficient.constant_nonneg Q κ M
    (A k) (k+1) p (Babs k) (B0 k) hβ hβsmall)

/-- The exact finite collection of actual reference-prefix caps has one
structural constant; no infinite-depth estimate is involved. -/
theorem cap(Q:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(N p:ℕ)
    (A:Fin N→ℝ)(Babs B0:Fin N→ℝ≥0){β Λ m H R:ℝ}(hβ:0<β)(hβsmall:β≤4/25)
    (hΛ:1≤Λ)(hm:0≤m)(hH0:0≤H)(hH1:H≤1)(hR:1≤R):
    let K:=fun k:Fin N=>MixedNativeReferenceGaussianFamily.coefficients Q κ M Λ (m^2) H (A k)
      (k+1) p (Babs k) (B0 k) (SHE.rho β) (ActualReferenceMasterClosure.referenceExponent β) (β/100) (β/100)
    (∑k:Fin N,∑i:Fin 3,Real.sqrt (K k i).toReal*
      StateBands.geometricConstant (NativeReferenceMasterCoefficient.degrees β (k+1) i/2)*
        R^(-(NativeReferenceMasterCoefficient.degrees β (k+1) i/2)))≤
      constant Q κ M N p A Babs B0 β*
        (NativeReferenceMasterCoefficient.linear β Λ*m+
          Λ^(-β/100)*m^(ActualReferenceMasterClosure.referenceExponent β)):=by
  intro K
  calc
    _≤∑k:Fin N,NativeReferenceMasterCoefficient.constant Q κ M (A k) (k+1) p (Babs k) (B0 k) β*
        (NativeReferenceMasterCoefficient.linear β Λ*m+
          Λ^(-β/100)*m^(ActualReferenceMasterClosure.referenceExponent β)):=by
      apply Finset.sum_le_sum
      intro k _
      exact NativeReferenceMasterCoefficient.cap Q κ M (A k) (k+1) p (Babs k) (B0 k)
        hβ hβsmall hΛ hm hH0 hH1 hR
    _=_:=by rw [←Finset.sum_mul];rfl

variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

/-- The literal scalar reference-prefix constant is independent of the
canonical companion smoothing index. -/
theorem canonical(n:ℕ)(κ M A:ℝ)(k p:ℕ)(Babs B0:ℝ≥0):
    NativeReferenceMasterCoefficient.constant (Smooth n) κ M A k p Babs B0 D.beta=
      NativeReferenceMasterCoefficient.constant Rough κ M A k p Babs B0 D.beta:=by
  have hh:=PastReferenceConstantUniform.canonical D hT hT1 hsmall n κ M k p Babs B0
    (SHE.rho D.beta) (ActualReferenceMasterClosure.referenceExponent D.beta) (D.beta/100) (D.beta/100)
  have hr:NativeReferenceMasterCoefficient.rawConstants (Smooth n) κ M A k p Babs B0 D.beta=
      NativeReferenceMasterCoefficient.rawConstants Rough κ M A k p Babs B0 D.beta:=by
    unfold NativeReferenceMasterCoefficient.rawConstants
    rw [hh.1,hh.2.1,hh.2.2]
  unfold NativeReferenceMasterCoefficient.constant
  rw [hr]

theorem canonical_finite(n:ℕ)(κ M:ℝ)(N p:ℕ)(A:Fin N→ℝ)(Babs B0:Fin N→ℝ≥0):
    constant (Smooth n) κ M N p A Babs B0 D.beta=constant Rough κ M N p A Babs B0 D.beta:=by
  unfold constant
  exact Finset.sum_congr rfl (fun k _=>canonical D hT hT1 hsmall n κ M (A k) (k+1) p (Babs k) (B0 k))
end SHE.NativeReferenceMasterFiniteCoefficient
