module

public import SHE.FiniteWeightedAssignmentMoments
public import SHE.MixedPastOmittedMoments
public import SHE.MinimumGapChoice
public import SHE.MixedPastAssignedMoments
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedPastJointData
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastOmittedWord
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastOmittedWord_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastOmittedWord_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastOmittedWord_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastOmittedWord_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastOmittedWord_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastOmittedWord_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile

variable (θ : ℝ)

local instance mixedPastOmittedWord_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastOmittedWord_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

def factor (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ) (age : Fin m→ℝ)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (A0 ν : ℝ) : ℝ :=
  VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
    ∏ j∈Finset.univ.erase j0,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (age j)
      (MinimumGapChoice.blockChoice lo hi choices j.succ)

/-- An erased factor is constant before centering, so every assignment
into it is identically zero. Those assignments contribute ZERO to the
time total as well; no spurious old-gap singularity is introduced. -/
def total (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ) (age : Fin m→ℝ)
    (j0 : Fin m) (A0 ν : ℝ) : ℝ :=
  ((assignments (m:=m+1) (List.finRange r)).map (fun choices=>
    if block choices j0.succ=[] then |factor (d:=d) P lo hi age choices j0 A0 ν| else 0)).sum

theorem total_nonneg (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ) (age : Fin m→ℝ)
    (j0 : Fin m) (A0 ν : ℝ) : 0≤total (d:=d) P lo hi age j0 A0 ν := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨choices,_,rfl⟩:=List.mem_map.mp hx
  split_ifs <;> positivity

theorem factor_le_total (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ)
    (age : Fin m→ℝ) (j0 : Fin m) (A0 ν : ℝ) (choices : List (Fin r×Fin (m+1)))
    (hc : choices∈assignments (m:=m+1) (List.finRange r)) (hz : block choices j0.succ=[]) :
    |factor (d:=d) P lo hi age choices j0 A0 ν|≤total (d:=d) P lo hi age j0 A0 ν := by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨cs,_,rfl⟩:=List.mem_map.mp hx
    split_ifs <;> positivity
  · exact List.mem_map.mpr ⟨choices,hc,ite_eq_left hz⟩

def momentConstant (P : CanonicalCovariance.ProfileParameters) (r m b : ℕ) (j0 : Fin m) (C0 : ℝ) : ℝ :=
  ((1/2:ℝ)^r)^(2*b)*((assignments (m:=m+1) (List.finRange r)).length:ℝ)^(2*b-1)*
    ((assignments (m:=m+1) (List.finRange r)).map
      (fun choices=>max (OmittedAssignedMoments.constant P r m choices j0 b C0) 0)).sum

theorem momentConstant_nonneg (P : CanonicalCovariance.ProfileParameters) (r m b : ℕ)
    (j0 : Fin m) (C0 : ℝ) : 0≤momentConstant P r m b j0 C0 := by
  unfold momentConstant
  apply mul_nonneg (by positivity)
  apply List.sum_nonneg
  intro x hx
  obtain ⟨cs,_,rfl⟩:=List.mem_map.mp hx
  exact le_max_right _ _

def average (P : CanonicalCovariance.ProfileParameters) (v q : ℝ≥0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (D : Fin r→State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n) (j0 : Fin m)
    (F : State d→ℝ) (ω : Ω) : ℝ :=
  (1/2:ℝ)^r*((assignments (m:=m+1) (List.finRange r)).map (fun choices=>
    if block choices j0.succ=[] then OmittedAssignedMoments.fibreAverage P Λ
      (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
      (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
      θ ((q:ℝ)-(v:ℝ)) σ target center lo hi
      (MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center ω)
      D g leaf choices j0 F else 0)).sum

include hIJ₀ hIJ₁ in
/-- The COMPLETE omitted-baseline word obeys actual random-past
conditional moment bounds against an arbitrary correlated past weight.
All erased-leaf assignments vanish exactly; all surviving root and rough
blocks keep the true minimum gap and original native age. -/
theorem moment_with_past_weight (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)-(v:ℝ)≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (D : Fin r→State n)
    (hD : ∀ ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (j0 : Fin m) (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ r F) (hfb : ∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)
    (K : ℝ) (hK : 0≤K)
    (hscore : ∀ ω,|∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j) (D j)|≤K)
    (weight : Ω→ℝ) (hw : Measurable[𝓕 v] weight) (hw0 : ∀ ω,0≤weight ω)
    (hwi : Integrable weight μ) :
    let G:=average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ P v q σ target center lo hi D g leaf j0 F
    Integrable (fun ω=>weight ω*|G ω|^(2*b)) μ ∧ (∫ ω,weight ω*|G ω|^(2*b) ∂μ)≤
      momentConstant P r m b j0 ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
        (K*total (d:=d) P lo hi (fun j=>target (leaf j)) j0 A0 ν)^(2*b)*(∫ ω,weight ω ∂μ) := by
  intro G
  let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  let dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  let mean:=MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  let cs:=assignments (m:=m+1) (List.finRange r)
  let T:=total (d:=d) P lo hi (fun j=>target (leaf j)) j0 A0 ν
  let C0:=(m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent
  let W:=fun choices ω=>if block choices j0.succ=[] then OmittedAssignedMoments.fibreAverage P Λ
    (U ω) (dir ω) θ ((q:ℝ)-(v:ℝ)) σ target center lo hi (mean ω) D g leaf choices j0 F else 0
  have hT : 0≤T:=total_nonneg P lo hi _ j0 A0 ν
  have hM : 0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hC0 : 0≤C0:=by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.rpow_nonneg
    unfold NativeHybridMoments.momentConstant
    exact mul_nonneg B0.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)
  have hU : Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hdir : Measurable dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm:=MixedPastJointData.mean_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  have hW (choices) (_hc:choices∈cs) : Measurable (W choices) := by
    by_cases hz:block choices j0.succ=[]
    · simpa only [W,ite_eq_left hz] using OmittedAssignedMoments.fibreAverage_measurable
        P Λ θ ((q:ℝ)-(v:ℝ)) U dir hU hdir σ target center lo hi mean hm (fun _=>D)
        (fun _=>measurable_const) g leaf choices j0 F hFm
    · simpa only [W,ite_eq_right hz] using (measurable_const (a:=(0:ℝ)) : Measurable (fun _ : Ω=>(0:ℝ)))
  have hbound (choices) (hc:choices∈cs) :
      Integrable (fun ω=>weight ω*|W choices ω|^(2*b)) μ ∧
      (∫ ω,weight ω*|W choices ω|^(2*b) ∂μ)≤
        max (OmittedAssignedMoments.constant P r m choices j0 b C0) 0*(K*T)^(2*b)*(∫ ω,weight ω ∂μ) := by
    have hC:=OmittedAssignedMoments.constant_nonneg P b choices j0 hC0
    rw [max_eq_left hC]
    by_cases hz:block choices j0.succ=[]
    · have hnd : (choices.map Prod.fst).Nodup:=by
        rw [assignment_coordinates _ _ hc]
        exact List.nodup_finRange r
      have hlen : (block choices 0).length≤r:=by
        simpa only [Fintype.card_fin] using (block_nodup choices hnd 0).length_le_card
      have hg (ω:Ω) : |(∏ j,scoreVariance
          (familyCovariance σ target center (referenceProfile P Λ (U ω) (dir ω)) lo hi j) (D j))*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
          ∏ j∈Finset.univ.erase j0,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi
            (target (leaf j)) (MinimumGapChoice.blockChoice lo hi choices j.succ)|≤K*T := by
        rw [mul_assoc,abs_mul]
        exact mul_le_mul (hscore ω) (factor_le_total P lo hi _ j0 A0 ν choices hc hz) (abs_nonneg _) hK
      have hh:=MixedPastOmittedMoments.assigned_moment_with_past_weight
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
        v q hvq hqH hspan σ target center hσ hσ1 hages hgap lo hi hlo hlohi hstop hdisjoint D hD
        g leaf hnative ht choices hnd j0 (fun j=>MinimumGapChoice.blockChoice lo hi choices j.succ)
        (fun j h=>MinimumGapChoice.blockChoice_mem lo hi choices j.succ h) F hFm hA0 hν
        (hf.of_le (by exact_mod_cast hlen)) (fun j hj=>hfb j (hj.trans hlen)) b hb B0 hBDG (K*T)
        (mul_nonneg hK hT) hg weight hw hw0 hwi
      simpa only [W,ite_eq_left hz] using hh
    · simp only [W,ite_eq_right hz,abs_zero,zero_pow (by omega : 2*b≠0),mul_zero,integral_zero]
      exact ⟨integrable_zero _ _ _,mul_nonneg (mul_nonneg hC (pow_nonneg (mul_nonneg hK hT) _))
        (integral_nonneg hw0)⟩
  have hh:=FiniteAssignmentMoments.weighted_moment_sum μ cs W hW weight
    (hw.mono (𝓕.le v) le_rfl) hw0 b hb (fun choices hc=>(hbound choices hc).1)
    (fun choices=>max (OmittedAssignedMoments.constant P r m choices j0 b C0) 0*(K*T)^(2*b)*(∫ ω,weight ω ∂μ))
    (fun choices hc=>(hbound choices hc).2)
  have hpow (ω) : weight ω*|G ω|^(2*b)=
      ((1/2:ℝ)^r)^(2*b)*(weight ω*|(cs.map (fun choices=>W choices ω)).sum|^(2*b)) := by
    simp only [G,average,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_pow]
    ring
  constructor
  · exact (hh.1.const_mul (((1/2:ℝ)^r)^(2*b))).congr (ae_of_all _ (fun ω=>(hpow ω).symm))
  · simp_rw [hpow]
    rw [integral_const_mul]
    have hfinal:=mul_le_mul_of_nonneg_left hh.2 (show 0≤((1/2:ℝ)^r)^(2*b) by positivity)
    simp only [List.sum_map_mul_right] at hfinal
    simpa only [momentConstant,C0,T,mul_assoc] using hfinal

end SHE.MixedPastOmittedWord


