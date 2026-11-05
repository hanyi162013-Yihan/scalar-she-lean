module

public import SHE.ParametricAssignedMoments
public import SHE.NativePairWindowLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.NativeAssignedLeafMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
open scoped NNReal ENNReal BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

def emptyConstant (P : CanonicalCovariance.ProfileParameters) (b : ℕ) (B : ℝ≥0) (κ M : ℝ) : ℝ :=
  (2:ℝ)^(2*b-1)*((NativeHybridMoments.momentConstant b B κ M)^P.exponent+
    GaussianCenteredLeafMoments.leafMomentConstant b P.exponent*
      ((ProfileVariance.upperConstant*P.upper)^(P.exponent/2))^(2*b))

def leafConstant {r k : ℕ} (P : CanonicalCovariance.ProfileParameters) (b : ℕ) (B : ℝ≥0) (κ M : ℝ)
    (choices : List (Fin r×Fin k)) (factor : Fin k) : ℝ :=
  if block choices factor=[] then emptyConstant P b B κ M
  else GaussianAudit.gaussianAbsMoment (((2*b:ℕ):ℝ)*P.exponent)

def leafScale {r k : ℕ} (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r×Fin k)) (factor : Fin k) (lo hi : Fin r→ℝ) (age : ℝ)
    (chosen : block choices factor≠[]→Fin r) : ℝ :=
  if h : block choices factor=[] then P.holder*age^(P.exponent/4)
  else (2:ℝ)^((block choices factor).length-1)*P.holder*
    (ProfileVariance.upperConstant*(P.lower/2))^(P.exponent/2)*
      (hi (chosen h)-lo (chosen h))^(P.exponent/4)

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Actual native current-state assigned leaves have deterministic
full-age gains when unassigned, and their original selected old-gap
gains when assigned. Every suppression and the FULL profile baseline is
retained. Conditional BDG, Gaussian Fubini and the true pair resolvent
discharge all current-mean displacement moments; no independence input
or compatibility of the random current mean is assumed. -/
theorem even_moment (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {n r k : ℕ} (σ target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hgap : ∀ i,(q:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    {θ : ℝ} (hθ : |θ|≤1) (i : Fin n) (hnative : σ i=target i)
    (ht : target i∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (chosen : block choices factor≠[]→Fin r) (hchosen : ∀ h,chosen h∈block choices factor)
    (b : ℕ) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower b J B0) :
    let u := embed u₀
    let d := embed (v₀-u₀)
    let center := nativeCenter centers
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let m := NativePairWindowLeaf.futureMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers θ
    let F := fun z : Ω×((Fin r→State n)×State n) =>
      ControlledAssignedLeaf.leaf choices factor P.coefficient (m z.1) i
        (ControlledProfile.profile P Λ u d (θ,(target i,center i))) z.2
    Integrable (fun z => |F z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|F z|^(2*b) ∂μ.prod νG)≤leafConstant P b B0 κ M choices factor*
        (leafScale P choices factor lo hi (target i) chosen)^(2*b) := by
  intro u d center A B νG m F
  have hm : Measurable m := NativePairWindowLeaf.futureMean_measurable 𝓕 μ H Λ κ hκ ha hell hb
    I₀ I₁ u₀ v₀ S q target centers hgap θ
  by_cases hblock : block choices factor=[]
  · have hh := NativePairWindowLeaf.even_moment 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      J hIJ₀ hIJ₁ P hΛ q hqH hq1 σ target centers hages hgap lo hi hlo hdisjoint hθ i hnative ht
      (suppressed choices factor) b B0 hBDG
    have he : F=(fun z : Ω×((Fin r→State n)×State n) =>
        P.coefficient (m z.1 i+((∑ j,suppress (suppressed choices factor) z.2.1 j)+z.2.2) i)-
          ControlledProfile.profile P Λ u d (θ,(target i,center i))) := by
      funext z
      exact ControlledAssignedLeaf.leaf_empty choices factor hblock _ _ _ _ _
    dsimp only at hh
    have he' := he
    dsimp only [m,u,d,center] at he'
    have hez (z : Ω×((Fin r→State n)×State n)) := congrFun he' z
    simp_rw [←hez] at hh
    refine ⟨hh.1,hh.2.trans ?_⟩
    have hqpow : (q:ℝ)^((b:ℝ)*P.exponent/2)≤(target i)^((b:ℝ)*P.exponent/2) :=
      rpow_le_rpow q.2 (hgap i).le
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) P.exponent_pos.le) (by norm_num))
    have htp : (target i)^((b:ℝ)*P.exponent/2)=((target i)^(P.exponent/4))^(2*b) := by
      rw [←Real.rpow_mul_natCast (ht.1.le)]
      congr 1
      push_cast
      ring
    have hs : P.holder^(2*b)*(NativeHybridMoments.momentConstant b B0 κ M)^P.exponent*
        (q:ℝ)^((b:ℝ)*P.exponent/2)≤
      P.holder^(2*b)*(NativeHybridMoments.momentConstant b B0 κ M)^P.exponent*
        ((target i)^(P.exponent/4))^(2*b) := by
      rw [←htp]
      exact mul_le_mul_of_nonneg_left hqpow (mul_nonneg (pow_nonneg P.holder_nonneg _)
        (rpow_nonneg (by
          have hM : 0≤M := hell.le.trans ((hb 0).1.trans (hb 0).2)
          dsimp [NativeHybridMoments.momentConstant]
          exact mul_nonneg B0.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)) _))
    change (2:ℝ)^(2*b-1)*_≤_
    calc
      _ ≤ (2:ℝ)^(2*b-1)*(P.holder^(2*b)*(NativeHybridMoments.momentConstant b B0 κ M)^P.exponent*
          ((target i)^(P.exponent/4))^(2*b)+
        GaussianCenteredLeafMoments.leafMomentConstant b P.exponent*
          (P.holder*(ProfileVariance.upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4))^(2*b)) :=
        mul_le_mul_of_nonneg_left (add_le_add hs le_rfl) (by positivity)
      _ = _ := by simp only [leafConstant,leafScale,hblock,ite_true,dite_true,emptyConstant,mul_pow];ring
  · have hfiber (ω : Ω) := WindowAssignedFactors.leaf_even_moment P Λ u d θ lo hi hdisjoint
      σ target center hσ hσ1 hages q.2 hlo hlohi hstop (m ω) i hnative ht choices hnd factor chosen hchosen b
    have hf : Measurable F := ParametricAssignedMoments.leaf_measurable choices factor
      P.coefficient P.measurable m hm i _
    have hh := UniformFiberMoments.even_moment μ νG F hf b
      (GaussianAudit.gaussianAbsMoment (((2*b:ℕ):ℝ)*P.exponent)*
        (leafScale P choices factor lo hi (target i) chosen)^(2*b))
      (fun ω => (hfiber ω).1) (fun ω => by
        have hhb := (hfiber ω).2
        simp only [WindowAssignedFactors.leafConstant,WindowAssignedFactors.leafScale,
          leafScale,hblock,ite_false,dite_false] at hhb ⊢
        convert! hhb using 1)
    simpa only [leafConstant,hblock,ite_false] using hh

end SHE.NativeAssignedLeafMoments
