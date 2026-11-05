module

public import SHE.FiniteAssignmentMoments
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

namespace SHE.MixedPastWordMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastWordMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastWordMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastWordMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastWordMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastWordMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastWordMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance mixedPastWordMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastWordMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}


/-- All original root clips and the minimum of each assigned rough block.
The empty block keeps its full native observation age. -/
def factor (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ)
    (age : Fin m→ℝ) (choices : List (Fin r×Fin (m+1))) (A0 ν : ℝ) : ℝ :=
  VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d *
    ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (age j)
      (MinimumGapChoice.blockChoice lo hi choices j.succ)

def total (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ)
    (age : Fin m→ℝ) (A0 ν : ℝ) : ℝ :=
  ((assignments (m:=m+1) (List.finRange r)).map
    (fun choices=>|factor (d:=d) P lo hi age choices A0 ν|)).sum

theorem total_nonneg (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ)
    (age : Fin m→ℝ) (A0 ν : ℝ) : 0 ≤ total (d:=d) P lo hi age A0 ν := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨cs,_,rfl⟩:=List.mem_map.mp hx
  exact abs_nonneg _

theorem factor_le_total (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ)
    (age : Fin m→ℝ) (A0 ν : ℝ) (choices : List (Fin r×Fin (m+1)))
    (hc : choices∈assignments (m:=m+1) (List.finRange r)) :
    |factor (d:=d) P lo hi age choices A0 ν| ≤ total (d:=d) P lo hi age A0 ν := by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨cs,_,rfl⟩:=List.mem_map.mp hx
    exact abs_nonneg _
  · exact List.mem_map.mpr ⟨choices,hc,rfl⟩

def momentConstant (P : CanonicalCovariance.ProfileParameters) (r m b : ℕ) (C0 : ℝ) : ℝ :=
  ((1/2:ℝ)^r)^(2*b)*((assignments (m:=m+1) (List.finRange r)).length:ℝ)^(2*b-1)*
    ((assignments (m:=m+1) (List.finRange r)).map (fun choices=>
      max (FullResidualAssignedMoments.constant P r m choices b C0) 0)).sum

theorem momentConstant_nonneg (P : CanonicalCovariance.ProfileParameters) (r m b : ℕ) (C0 : ℝ) :
    0 ≤ momentConstant P r m b C0 := by
  unfold momentConstant
  apply mul_nonneg (by positivity)
  apply List.sum_nonneg
  intro x hx
  obtain ⟨cs,_,rfl⟩:=List.mem_map.mp hx
  exact le_max_right _ _

/-- The complete old-score assignment sum, before any spatial average.
The Gaussian laws depend on the actual past states and the current
mean is the actual theta-interpolated mixed-pair observation. -/
def average (P : CanonicalCovariance.ProfileParameters) (v q : ℝ≥0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (second : Bool) (D : Fin r→State n) (E : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (F : State d→ℝ) (ω : Ω) : ℝ :=
  (1/2:ℝ)^r*((assignments (m:=m+1) (List.finRange r)).map (fun choices=>
    MixedPastAssignedMoments.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ
      P v q σ target center lo hi second D E g leaf choices F ω)).sum

include hIJ₀ hIJ₁ in
/-- Conditional moments of the full, correlated all-order assignment
sum. The sharp time factor stays outside the dimensional constant.
The only geometric input is a uniform cap of the actual old and fresh
score energies, for which common-profile physical envelopes are proved
separately. No independence or fixed-covariance substitution is used. -/
theorem moment_on_past_event (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0 ≤ Λ) (hθ : |θ| ≤ 1)
    (v q : ℝ≥0) (hvq : v ≤ q) (hqH : q ≤ H) (hspan : (q:ℝ)-(v:ℝ) ≤ 1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i ≤ 1) (hages : ∀ i,σ i ≤ target i)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)-(v:ℝ) ≤ lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i ≤ lo j ∨ hi j ≤ σ i)
    (hdisjoint : ∀ j l,j≠l→hi j ≤ lo l ∨ hi l ≤ lo j)
    (second : Bool) (D : Fin r→State n) (E : State n)
    (hD : ∀ ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j)).range)
    (hE : ∀ ω,E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (fixedProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) lo hi)
        σ target center ((q:ℝ)-(v:ℝ)) θ)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ContDiff ℝ r F)
    (hfb : ∀ j,j ≤ r→∀ z,‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)
    (K : ℝ) (hK : 0 ≤ K)
    (hscore : ∀ ω,
      let u := MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω
      let dir := MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω
      let A := familyCovariance σ target center (referenceProfile P Λ u dir) lo hi
      let B := ControlledFixedReserve.covariance P Λ u dir (fixedProfile P Λ u dir lo hi) σ target center ((q:ℝ)-(v:ℝ)) θ
      |(∏ j,scoreVariance (A j) (D j))*scale second B E| ≤ K)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    let G := average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ P v q σ target center lo hi
      second D E g leaf F
    Integrable (fun ω=>|G ω|^(2*b)) (μ.restrict A) ∧
      (∫ ω in A,|G ω|^(2*b) ∂μ) ≤ 
        momentConstant P r m b ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
          (K*total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν)^(2*b)*μ.real A := by
  intro G
  let cs:=assignments (m:=m+1) (List.finRange r)
  let W:=fun choices=>MixedPastAssignedMoments.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ
    P v q σ target center lo hi second D E g leaf choices F
  let T:=total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν
  let C0:=(m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent
  let C:=fun choices=>max (FullResidualAssignedMoments.constant P r m choices b C0) 0
  have hnd (choices) (hc:choices∈cs) : (choices.map Prod.fst).Nodup := by
    rw [assignment_coordinates _ _ hc]
    exact List.nodup_finRange r
  have hlen (choices) (hc:choices∈cs) : (block choices 0).length ≤ r := by
    simpa only [Fintype.card_fin] using (block_nodup choices (hnd choices hc) 0).length_le_card
  have hbound (choices) (hc:choices∈cs) := MixedPastAssignedMoments.moment_on_past_event
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ v q hvq hqH hspan
    σ target center hσ hσ1 hages hgap lo hi hlo hlohi hstop hdisjoint second D E hD hE g leaf hnative ht
    choices (hnd choices hc) (fun j=>MinimumGapChoice.blockChoice lo hi choices j.succ)
    (fun j h=>MinimumGapChoice.blockChoice_mem lo hi choices j.succ h)
    F hFm hA0 hν (hf.of_le (by exact_mod_cast hlen choices hc))
    (fun j hj z=>hfb j (hj.trans (hlen choices hc)) z) b hb0 B0 hBDG (K*T)
    (mul_nonneg hK (total_nonneg (d:=d) P lo hi _ A0 ν)) (fun ω=>by
      have hh:=mul_le_mul (hscore ω) (factor_le_total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν choices hc)
        (abs_nonneg _) hK
      convert! hh using 1 <;> simp only [factor,abs_mul,mul_assoc]) A hA
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hdir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm := MixedPastJointData.mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  have hW (choices) (_hc:choices∈cs) : Measurable (W choices) :=
    VaryingControlledGaussianFields.fibreAverage_measurable P Λ θ ((q:ℝ)-(v:ℝ)) _ _ hU hdir
      σ target center lo hi _ hm second (fun _=>D) (fun _=>measurable_const) (fun _=>E) measurable_const g leaf choices F hFm
  have hterm (choices) (hc:choices∈cs) :
      (∫ ω in A,|W choices ω|^(2*b) ∂μ) ≤ C choices*(K*T)^(2*b)*μ.real A :=
    (hbound choices hc).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (mul_nonneg hK (total_nonneg (d:=d) P lo hi _ A0 ν)) _))
      (measureReal_nonneg))
  have hsum:=FiniteAssignmentMoments.moment_sum (μ.restrict A) cs W hW b hb0
    (fun choices hc=>(hbound choices hc).1) (fun choices=>C choices*(K*T)^(2*b)*μ.real A) hterm
  have he (ω:Ω) : |G ω|^(2*b)=((1/2:ℝ)^r)^(2*b)*|(cs.map (fun choices=>W choices ω)).sum|^(2*b) := by
    simp only [G,average,cs,W,abs_mul,abs_of_nonneg (by positivity:0 ≤ (1/2:ℝ)^r),mul_pow]
  constructor
  · exact (hsum.1.const_mul _).congr (ae_of_all _ (fun ω=>(he ω).symm))
  · simp_rw [he]
    rw [integral_const_mul]
    have hh:=mul_le_mul_of_nonneg_left hsum.2 (show 0 ≤ ((1/2:ℝ)^r)^(2*b) by positivity)
    rw [List.sum_map_mul_right,List.sum_map_mul_right] at hh
    exact hh.trans_eq (by dsimp only [momentConstant,C,C0,cs,T];ring)

end SHE.MixedPastWordMoments
